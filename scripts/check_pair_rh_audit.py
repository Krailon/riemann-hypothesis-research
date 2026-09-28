#!/usr/bin/env python3
"""Validate the structure and freshness of the recorded pair RH review.

Task: verification. Assumptions: UNCONDITIONAL for finite bookkeeping.
This is not a mathematical proof checker or an independent source review.
Only the standard library is used. Audit verdicts are manually authored.
"""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / 'research/pair-rh-audit.json'
MAIN = 'proofs/pair_baseline.tex'
LEDGER = 'research/theorem-ledger.yaml'
KINDS = {'nonmathematical', 'exposition', 'definition', 'statement',
         'proof', 'imported_input', 'conditional_check'}
VERDICTS = {'justified', 'isolated_conditional_check', 'unresolved'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON key: {key}')
        result[key] = value
    return result


def load_record():
    return json.loads(RECORD.read_text(), object_pairs_hook=unique_object)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def indexed_blocks(text):
    """Index the ledger's existing top-level list entries, not general YAML."""
    matches = list(re.finditer(r'^  - id: ([A-Z0-9-]+)\s*$', text, re.M))
    blocks = {}
    for i, match in enumerate(matches):
        key = match[1]
        require(key not in blocks, f'duplicate ledger ID: {key}')
        end = matches[i+1].start() if i+1 < len(matches) else len(text)
        blocks[key] = text[match.end():end]
    return blocks


def field(block, name):
    values = re.findall(r'^    ' + re.escape(name) + r': (.+)$', block, re.M)
    require(len(values) == 1, f'unsupported/missing ledger field: {name}')
    return values[0]


def id_list(value):
    # Audited claims currently use one-line lists. Fail closed on new syntax.
    require(re.fullmatch(r'\[(?:[A-Z0-9_-]+(?:, [A-Z0-9_-]+)*)?\]', value),
            f'unsupported ledger list: {value}')
    return [] if value == '[]' else value[1:-1].split(', ')


def validate(record, read=None):
    """Raise ValueError for stale/incomplete/inconsistent review records.

    read is injectable for tests that edit virtual source bytes. A matching
    hash does not establish that the manual mathematical verdict is correct.
    """
    if read is None:
        read = lambda path: (ROOT / path).read_bytes()
    require(record['schema_version'] == 1, 'unsupported audit schema')
    require(record['assumptions'] == ['UNCONDITIONAL'], 'audit task assumptions')
    require(record['independent_review'] is False, 'independent review not performed')
    require(record['analytic_proof_certificate'] is False, 'not an analytic certificate')
    ledger = read(LEDGER)
    require(digest(ledger) == record['ledger_sha256'], 'stale ledger hash')
    blocks = indexed_blocks(ledger.decode())
    snapshots = record['claim_snapshot']
    source_ids = record['source_node_ids']
    require(len(source_ids) == len(set(source_ids)), 'duplicate source node')
    require(set(source_ids) <= blocks.keys(), 'unknown source node')
    for key, expected in snapshots.items():
        require(key in blocks, f'unknown claim: {key}')
        block = blocks[key]
        used = field(block, 'computation_used_in_proof')
        require(used in {'true', 'false'}, 'unsupported computational flag')
        actual = dict(status=field(block, 'status'),
                      assumptions=id_list(field(block, 'assumptions')),
                      dependencies=id_list(field(block, 'dependencies')),
                      computation_used_in_proof=used == 'true')
        require(actual == expected, f'changed claim snapshot: {key}')
        require(actual['assumptions'] == ['UNCONDITIONAL'], f'conditional claim: {key}')
    root_claim = record['root_claim']
    require(root_claim == 'PAIR-ASYMPTOTIC-001', 'wrong audit root')
    seen, active = set(), set()

    def visit(key):
        require(key not in active, f'dependency cycle: {key}')
        if key in seen:
            return
        require(key in snapshots or key in source_ids, f'missing dependency: {key}')
        seen.add(key)
        if key in source_ids:
            return
        active.add(key)
        for dep in snapshots[key]['dependencies']:
            visit(dep)
        active.remove(key)

    visit(root_claim)
    require('PAIR-BGSTB-001' not in seen, 'headline theorem used as premise')
    require(set(snapshots) == (seen - set(source_ids)) | {'PAIR-TRANSLATION-001'},
            'snapshot must cover closure plus separate translation')
    require(set(source_ids) == seen & set(source_ids), 'extraneous provenance node')
    evidence = {}
    for item in record['evidence']:
        require(item['id'] not in evidence, 'duplicate evidence ID')
        require(item['claim_id'] in snapshots, 'unknown evidence claim')
        require(item['locator'].strip() and item['urls'], 'missing source locator')
        require(all(url.startswith('https://') for url in item['urls']), 'invalid source URL')
        require(item['reviewed_on'] == record['reviewed_on'], 'source review date mismatch')
        evidence[item['id']] = item
    imported = {key for key in seen - set(source_ids)
                if field(blocks[key], 'kind') == 'imported_theorem'}
    require(len(evidence) == len(imported) and
            {e['claim_id'] for e in evidence.values()} == imported,
            'imported statement evidence coverage')
    paths, passage_ids, covered_claims = set(), set(), set()
    unresolved = []
    main_conditional = 0
    for file in record['files']:
        path = file['path']
        require(not Path(path).is_absolute() and '..' not in Path(path).parts,
                'source path outside repository')
        require(path not in paths, 'duplicate reviewed file')
        paths.add(path)
        raw = read(path)
        require(digest(raw) == file['sha256'], f'stale source hash: {path}')
        lines = raw.decode().splitlines()
        require(len(lines) == file['line_count'], f'changed line count: {path}')
        scope = file['coverage']
        require(scope in {'complete', 'selected_passages'}, 'unknown coverage scope')
        if path == MAIN:
            require(scope == 'complete', 'manuscript requires complete coverage')
        previous = 0
        require(file['passages'], 'empty reviewed file')
        for item in file['passages']:
            key = item['id']
            require(key not in passage_ids, f'duplicate passage: {key}')
            passage_ids.add(key)
            a, b = item['start_line'], item['end_line']
            require(type(a) is int and type(b) is int and
                    previous < a <= b <= len(lines), f'overlap/invalid range: {key}')
            if scope == 'complete':
                require(a == previous+1, f'coverage gap: {key}')
            previous = b
            kind, verdict = item['kind'], item['verdict']
            require(kind in KINDS and verdict in VERDICTS, f'unknown classification: {key}')
            require(item['reason'].strip(), f'missing justification: {key}')
            ids = item['claim_ids']
            require(set(ids) <= snapshots.keys(), f'unknown passage claim: {key}')
            require(len(ids) == len(set(ids)), f'duplicate passage claim: {key}')
            expected_assumptions = [] if kind == 'nonmathematical' else [
                'RH' if kind == 'conditional_check' else 'UNCONDITIONAL']
            require(item['assumptions'] == expected_assumptions,
                    f'assumption classification: {key}')
            require(bool(ids) == (kind != 'nonmathematical'), f'claim attribution: {key}')
            if kind == 'conditional_check':
                require(verdict == 'isolated_conditional_check', f'conditional verdict: {key}')
                require('RH' in '\n'.join(lines[a-1:b]) or
                        'rh_' in '\n'.join(lines[a-1:b]), f'unmarked RH check: {key}')
                if path == MAIN:
                    main_conditional += 1
            else:
                require(verdict != 'isolated_conditional_check', f'verdict mismatch: {key}')
            if verdict == 'unresolved':
                unresolved.append(key)
            for evidence_id in item['evidence_ids']:
                require(evidence_id in evidence, f'unknown evidence: {key}')
                require(evidence[evidence_id]['claim_id'] in ids, f'evidence mismatch: {key}')
            if kind == 'imported_input':
                require(item['evidence_ids'], f'uncited input: {key}')
            if path == MAIN and kind != 'conditional_check':
                covered_claims.update(ids)
        if scope == 'complete':
            require(previous == len(lines), f'unreviewed final lines: {path}')
    require(MAIN in paths, 'missing manuscript')
    require(main_conditional == 3, 'three manuscript RH specializations must be isolated')
    require(covered_claims == seen - set(source_ids), 'manuscript claim coverage')
    require(not unresolved, f'unresolved local passages: {unresolved}')
    require(record['outcome'] == 'no_contamination_found_in_reviewed_scope', 'outcome mismatch')
    require(record['obligations'] and all(o['scope'] == 'outside_current_review'
                                        for o in record['obligations']), 'obligation scope')
    return len(passage_ids)


class PairRHAuditStructure(unittest.TestCase):
    def setUp(self):
        self.record = load_record()

    def test_review_structure_and_freshness(self):
        self.assertGreater(validate(self.record), 100)

    def test_reject_gap_overlap_and_unreviewed_tail(self):
        for mutate in (lambda f: f['passages'][1].update(start_line=29),
                       lambda f: f['passages'][1].update(start_line=27),
                       lambda f: f['passages'].pop()):
            record = deepcopy(self.record)
            mutate(record['files'][0])
            with self.assertRaises(ValueError):
                validate(record)

    def test_reject_stale_proof_and_ledger_bytes(self):
        for changed in (MAIN, LEDGER):
            def read(path):
                raw = (ROOT / path).read_bytes()
                return raw + b'\n' if path == changed else raw
            with self.assertRaisesRegex(ValueError, 'stale'):
                validate(self.record, read)

    def test_reject_missing_dependency_and_changed_assumption(self):
        record = deepcopy(self.record)
        del record['claim_snapshot']['ZETA-COUNT-001']
        with self.assertRaises(ValueError):
            validate(record)
        record = deepcopy(self.record)
        record['claim_snapshot']['PAIR-NORM-001']['assumptions'] = ['RH']
        with self.assertRaises(ValueError):
            validate(record)

    def test_reject_unresolved_and_unisolated_checks(self):
        record = deepcopy(self.record)
        record['files'][0]['passages'][1]['verdict'] = 'unresolved'
        with self.assertRaisesRegex(ValueError, 'unresolved local'):
            validate(record)
        record = deepcopy(self.record)
        check = next(p for p in record['files'][0]['passages']
                     if p['kind'] == 'conditional_check')
        check['assumptions'] = ['UNCONDITIONAL']
        with self.assertRaisesRegex(ValueError, 'assumption classification'):
            validate(record)

    def test_reject_duplicate_and_unknown_references(self):
        for value in ('unknown claim', 'duplicate passage', 'unknown evidence'):
            record = deepcopy(self.record)
            passages = record['files'][0]['passages']
            if value == 'unknown claim':
                passages[1]['claim_ids'] = ['MISSING-001']
            elif value == 'duplicate passage':
                passages[1]['id'] = passages[0]['id']
            else:
                passages[4]['evidence_ids'] = ['missing']
            with self.assertRaises(ValueError):
                validate(record)
        with self.assertRaisesRegex(ValueError, 'duplicate JSON key'):
            json.loads('{"a":1,"a":2}', object_pairs_hook=unique_object)

    def test_reject_missing_imported_evidence(self):
        record = deepcopy(self.record)
        record['evidence'].pop()
        with self.assertRaisesRegex(ValueError, 'evidence coverage'):
            validate(record)


if __name__ == '__main__':
    unittest.main(verbosity=2)
