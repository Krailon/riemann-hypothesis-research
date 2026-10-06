#!/usr/bin/env python3
"""Check the recorded triple theorem dependency closure and its documentation.

Task: finite bookkeeping verification. Assumptions: UNCONDITIONAL for the
checker, with claim assumptions preserved verbatim. This checks recorded
edges and metadata, not analytic correctness or a new RH audit. Stdlib only.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import unittest

from check_pair_rh_audit import (
    field, id_list, indexed_blocks, require, unique_object, validate as validate_pair,
)

ROOT = Path(__file__).resolve().parents[1]
ROOT_CLAIM = 'TRIPLE-SMOOTHED-CORRELATION-001'
LEDGER = 'research/theorem-ledger.yaml'
RECORD = 'research/triple-dependency-graph.json'
REPORT = 'research/triple-dependency-graph.md'
PAIR_AUDIT = 'research/pair-rh-audit.json'
GROUPS = ('triple', 'pair_local', 'imported', 'provenance')
GROUP_NAMES = ('Triple claims', 'Inherited local pair claims', 'Imported claims',
               'Source provenance')


def read_file(path):
    return (ROOT / path).read_bytes()


def scalar(raw):
    """Only the simple scalar syntax used in the selected ledger fields."""
    if raw.startswith('"') or raw in ('true', 'false', 'null'):
        return json.loads(raw)
    require(raw not in ('|', '>') and not raw.startswith("'"),
            'unsupported scalar syntax')
    return raw


def subsection(block, name):
    match = re.search(r'^    '+re.escape(name)+r':\n((?:      [^\n]*\n)+)',
                      block, re.M)
    require(match is not None, 'missing subsection: '+name)
    return match[1]


def flat_section(raw):
    result = {}
    for line in raw.splitlines():
        match = re.fullmatch(r'      ([a-z_]+): (.+)', line)
        require(match is not None, 'unsupported source structure')
        require(match[1] not in result, 'duplicate source field')
        result[match[1]] = scalar(match[2])
    return result


def closure(root, dependencies):
    """Traverse only dependency edges, rejecting unknown nodes and cycles."""
    seen, active, edges = set(), set(), []
    def visit(key):
        require(key in dependencies, 'unknown dependency: '+key)
        require(key not in active, 'dependency cycle: '+key)
        if key in seen:
            return
        active.add(key)
        require(len(dependencies[key]) == len(set(dependencies[key])),
                'duplicate dependency: '+key)
        for dep in dependencies[key]:
            edges.append([key, dep])
            visit(dep)
        active.remove(key)
        seen.add(key)
    visit(root)
    return seen, sorted(edges)


def derive(read=read_file):
    ledger = read(LEDGER).decode()
    blocks = indexed_blocks(ledger)
    source_prefix = ledger.split('\nclaims:\n', 1)[0]
    source_ids = set(indexed_blocks(source_prefix))
    dependencies, pending = {}, [ROOT_CLAIM]
    while pending:
        key = pending.pop()
        require(key in blocks, 'unknown dependency: '+key)
        if key in dependencies:
            continue
        dependencies[key] = ([] if key in source_ids
                             else id_list(field(blocks[key], 'dependencies')))
        pending.extend(dependencies[key])
    seen, edges = closure(ROOT_CLAIM, dependencies)
    pair = json.loads(read(PAIR_AUDIT), object_pairs_hook=unique_object)
    validate_pair(pair, read=read)
    nodes = []
    for key in sorted(seen):
        block = blocks[key]
        node = dict(id=key, dependencies=dependencies[key],
                    ledger_block_sha256=hashlib.sha256(block.encode()).hexdigest())
        if key in source_ids:
            node.update(node_type='provenance', group='provenance',
                        source={name: scalar(field(block, name)) for name in
                                ('bibliography_key', 'version', 'locator', 'audit_status', 'notes')})
        else:
            kind = field(block, 'kind')
            node.update(node_type='claim', group=('imported' if kind == 'imported_theorem'
                        else 'triple' if key.startswith('TRIPLE-') else 'pair_local'),
                        kind=kind, title=scalar(field(block, 'title')),
                        status=field(block, 'status'), assumptions=field(block, 'assumptions'),
                        source=flat_section(subsection(block, 'source')),
                        project_audit_raw=subsection(block, 'project_audit'),
                        pair_audit_covered=key in pair['claim_snapshot'])
            for name in ('constants_effective', 'computation_used_in_proof',
                         'all_limit_interchanges_justified', 'dependency_graph_complete',
                         'certificate_artifact_hash'):
                node[name] = scalar(field(block, name))
            limits = re.findall(r'^    limit_order: (.+)$', block, re.M)
            require(len(limits) <= 1, 'duplicate limit order')
            node['limit_order'] = scalar(limits[0]) if limits else None
        nodes.append(node)
    counts = {g: sum(n['group'] == g for n in nodes) for g in GROUPS}
    return dict(schema_version=1, task='dependency_bookkeeping', root_claim=ROOT_CLAIM,
                ledger=LEDGER, traversal='dependencies_only', analytic_proof_certificate=False,
                counts=dict(claims=sum(n['node_type'] == 'claim' for n in nodes),
                            nodes=len(nodes), edges=len(edges), **counts),
                nodes=nodes, edges=edges,
                inherited_pair_audit=dict(record=PAIR_AUDIT, reviewed_on=pair['reviewed_on'],
                    independent_review=pair['independent_review'],
                    claim_ids=sorted(seen & pair['claim_snapshot'].keys())),
                triple_claims_outside_closure=sorted(k for k in blocks
                    if k.startswith('TRIPLE-') and k not in seen))


def escaped(value):
    if value is None:
        return 'null (unrecorded/unknown)'
    if isinstance(value, bool):
        return str(value).lower()
    return str(value).replace('|', '&#124;').replace('\n', '<br/>')


def code(value):
    return '`'+escaped(value)+'`'


def rows(header, data):
    return '\n'.join(['| '+' | '.join(header)+' |',
                       '| '+' | '.join('---' for _ in header)+' |']+
                      ['| '+' | '.join(row)+' |' for row in data])


def render_blocks(record):
    """Canonical derived parts; explanatory proof-scope prose stays authored."""
    nodes = record['nodes']
    ids = {n['id']: 'N'+str(i) for i, n in enumerate(nodes)}
    graph = ['```mermaid', 'flowchart TD']
    for group, title in zip(GROUPS, GROUP_NAMES):
        graph.append('    subgraph '+group+'["'+title+'"]')
        graph.extend('        '+ids[n['id']]+'["'+n['id']+'"]'
                     for n in nodes if n['group'] == group)
        graph.append('    end')
    graph.extend('    '+ids[a]+' --> '+ids[b] for a, b in record['edges'])
    graph.append('```')
    result = {'graph': '\n'.join(graph)}
    claims = [n for n in nodes if n['node_type'] == 'claim']
    for group in GROUPS[:-1]:
        data = []
        for n in claims:
            if n['group'] != group:
                continue
            source = n['source']
            data.append([code(n['id']), escaped(n['title']),
                ', '.join(map(code, n['dependencies'])) or 'None recorded', code(n['status']),
                code(n['assumptions']), '['+source['label']+'](../'+source['file']+')'])
        result[group] = rows(['Claim', 'Role', 'Direct dependencies', 'Status',
                              'Assumptions (verbatim ledger field)', 'Proof locator'], data)
    result['flags'] = rows(['Claim', 'Effective constants', 'Interchanges justified',
                            'Dependency completeness', 'Computation in proof'],
        [[code(n['id'])]+[escaped(n[k]) for k in ('constants_effective',
          'all_limit_interchanges_justified', 'dependency_graph_complete',
          'computation_used_in_proof')] for n in claims])
    result['limits'] = rows(['Claim', 'Recorded limit order'],
                           [[code(n['id']), escaped(n['limit_order'])] for n in claims])
    result['sources'] = rows(['Source pointer', 'Reached from', 'Bibliography / version',
                              'Locator', 'Recorded review status and scope'],
        [[code(n['id']), ', '.join(code(a) for a, b in record['edges'] if b == n['id']),
          code(n['source']['bibliography_key'])+' / '+code(n['source']['version']),
          escaped(n['source']['locator']), code(n['source']['audit_status'])+'; '+escaped(n['source']['notes'])]
         for n in nodes if n['node_type'] == 'provenance'])
    result['imported_sources'] = rows(['Imported claim', 'Primary-source locator',
                                       'Existing source-review record'],
        [[code(n['id']), '['+n['source']['bibliography_key']+']('+n['source']['url']+') — '+
          escaped(n['source']['locator']), escaped(n['project_audit_raw'].strip())]
         for n in claims if n['group'] == 'imported'])
    result['coverage'] = rows(['Inherited claim', 'Existing audit passages (file: ID)',
                               'Coverage scope'], audit_rows(record))
    result['outside'] = rows(['Earlier triple claim outside this dependency closure'],
                            [[code(k)] for k in record['triple_claims_outside_closure']])
    return result


def audit_rows(record):
    # Evidence is saved in the graph, so document rendering has no hidden reads.
    return [[code(k), '; '.join(escaped(p) for p in record['pair_passages'][k]),
             'Existing Work Package A review only']
            for k in record['inherited_pair_audit']['claim_ids']]


def expected_record(read=read_file):
    record = derive(read)
    pair = json.loads(read(PAIR_AUDIT), object_pairs_hook=unique_object)
    record['pair_passages'] = {k: [f['path']+': '+p['id'] for f in pair['files']
        for p in f['passages'] if k in p['claim_ids']]
        for k in record['inherited_pair_audit']['claim_ids']}
    require(all(record['pair_passages'].values()), 'missing inherited passage evidence')
    return record


def validate(record, report, read=read_file):
    expected = expected_record(read)
    require(record == expected, 'graph snapshot differs from ledger or existing audit')
    for name, content in render_blocks(expected).items():
        pattern = r'<!-- triple-dependencies:'+name+r':start -->\n(.*?)\n<!-- triple-dependencies:'+name+r':end -->'
        matches = re.findall(pattern, report, re.S)
        require(matches == [content], 'changed/missing/duplicate report block: '+name)
    bibliography = read('research/literature.bib').decode()
    for node in record['nodes']:
        source = node['source']
        if node['node_type'] == 'claim':
            path = source['file']
            require(not Path(path).is_absolute() and '..' not in Path(path).parts,
                    'invalid proof path')
            require(r'\label{'+source['label']+'}' in read(path).decode(),
                    'missing proof label: '+node['id'])
        if 'bibliography_key' in source:
            require(re.search(r'@\w+\{'+re.escape(source['bibliography_key'])+r',', bibliography),
                    'unknown bibliography key')
    for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', report):
        if target.startswith('https://'):
            continue
        path = Path(REPORT).parent/target.split('#', 1)[0]
        read(str(path))  # Missing local targets raise FileNotFoundError.
    return record['counts']


def load():
    return json.loads(read_file(RECORD), object_pairs_hook=unique_object)


class TripleDependencyChecks(unittest.TestCase):
    def test_current_graph_and_document(self):
        counts = validate(load(), read_file(REPORT).decode())
        self.assertEqual(counts, dict(claims=31, nodes=33, edges=58,
                         triple=15, pair_local=10, imported=6, provenance=2))

    def test_reject_missing_extra_and_duplicate_edges_and_nodes(self):
        baseline, report = load(), read_file(REPORT).decode()
        for change in ('missing_edge', 'extra_edge', 'duplicate_edge',
                       'missing_node', 'extra_node', 'duplicate_node'):
            r = deepcopy(baseline)
            if change == 'missing_edge': r['edges'].pop()
            if change == 'extra_edge': r['edges'].append([ROOT_CLAIM, 'PAIR-ASYMPTOTIC-001'])
            if change == 'duplicate_edge': r['edges'].append(r['edges'][0])
            if change == 'missing_node': r['nodes'].pop()
            if change == 'extra_node': r['nodes'].append({'id': 'UNKNOWN'})
            if change == 'duplicate_node': r['nodes'].append(r['nodes'][0])
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate(r, report)

    def test_reject_changed_support_metadata_and_false_audit_coverage(self):
        baseline, report = load(), read_file(REPORT).decode()
        for key, value in (('assumptions', '[UNCONDITIONAL]'),
                           ('status', 'independently-checked'),
                           ('pair_audit_covered', True),
                           ('constants_effective', False)):
            r = deepcopy(baseline)
            node = next(n for n in r['nodes'] if n['id'] == ROOT_CLAIM)
            node[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                validate(r, report)
        r = deepcopy(baseline)
        r['inherited_pair_audit']['claim_ids'].append(ROOT_CLAIM)
        with self.assertRaises(ValueError): validate(r, report)

    def test_unknown_dependencies_cycles_and_duplicate_ids(self):
        for graph in ({'A': ['B']}, {'A': ['B'], 'B': ['A']}, {'A': ['B', 'B'], 'B': []}):
            with self.assertRaises(ValueError): closure('A', graph)
        with self.assertRaises(ValueError): indexed_blocks('  - id: A\n  - id: A\n')
        with self.assertRaises(ValueError): json.loads('{"a":1,"a":2}', object_pairs_hook=unique_object)

    def test_reject_changed_mermaid_inventory_and_links(self):
        r, report = load(), read_file(REPORT).decode()
        for altered in (re.sub(r'(    N[0-9]+) --> (N[0-9]+)', r'\1 -.-> \2', report, count=1),
                        report.replace('| `TRIPLE-MASTER-001` |', '| `UNKNOWN` |', 1)):
            self.assertNotEqual(altered, report)
            with self.assertRaises(ValueError): validate(r, altered)
        with self.assertRaises(FileNotFoundError):
            validate(r, report+'\n[broken](nonexistent-dependency-target.md)\n')

    def test_reject_missing_proof_label(self):
        def read(path):
            raw = read_file(path)
            if path == 'proofs/triple_explicit_formula.tex':
                raw = raw.replace(b'\\label{thm:triple-smoothed-correlation}', b'')
            return raw
        with self.assertRaisesRegex(ValueError, 'missing proof label'):
            validate(load(), read_file(REPORT).decode(), read)

    def test_unknown_upstream_fields_and_closure_boundaries(self):
        r = load(); nodes = {n['id']: n for n in r['nodes']}
        self.assertIsNone(nodes['ZETA-COUNT-001']['all_limit_interchanges_justified'])
        self.assertIsNone(nodes['GAMMA-DIGAMMA-001']['limit_order'])
        for n in nodes.values():
            if n['node_type'] == 'claim':
                self.assertFalse(n['computation_used_in_proof'])
        self.assertEqual(len(r['inherited_pair_audit']['claim_ids']), 16)
        self.assertFalse({'ZETA-KV-001', 'ZETA-LOW-001', 'PAIR-ASYMPTOTIC-001',
                          'PAIR-BGSTB-001'} & nodes.keys())
        self.assertIn('TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001', nodes)
        self.assertIn('"SUPPORT(', nodes[ROOT_CLAIM]['assumptions'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
