#!/usr/bin/env python3
"""UNCONDITIONAL bookkeeping verification, not an analytic proof checker.

The coverage map records abstract Lean components and undischarged analytic
premises. It never promotes the historical correlation claims.
"""
import hashlib
import json
from pathlib import Path
import re
import unittest

from check_pair_rh_audit import indexed_blocks, field, id_list, require
from check_triple_dependencies import closure, flat_section, subsection

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / 'research/lean-analytic-coverage.json'
ROOTS = ['TRIPLE-SMOOTHED-CORRELATION-001', 'ORDINATE-CONSTANT-KERNEL-001',
         'ORDINATE-TRIPLE-001']
MODULES = ['OccurrenceSummability', 'OccurrenceLimits',
           'OccurrenceIntegration', 'SummabilityExamples']
PARTIAL = {
    'TRIPLE-SMOOTHED-CORRELATION-001': (
        ['triple_cutoff_limit', 'dominated_occurrence_limit'],
        ['Instantiate the occurrence model and all fixed-height absolute bounds.',
         'Formalize the stated main term and named errors; no uniform height majorant is supplied.']),
    'TRIPLE-MASTER-001': (
        ['integral_occurrence_sum', 'integral_occurrence_cutoff_limit'],
        ['Prove the actual kernel integrability and summable integral-norm bound.',
         'Formalize the explicit-formula expansion, prime-side sums and normalization.']),
    'TRIPLE-KERNEL-PROFILE-001': (
        ['dominated_integral_limit'],
        ['Formalize the rational kernel, residue evaluation and dominating function.',
         'Prove collision and parameter-endpoint limits with that domination.']),
    'ORDINATE-TRANSFER-001': (
        ['dyadic_summable_norm', 'dyadic_tail_bound', 'radius_decay_to_shell',
         'independent_sequence_cutoff_limit'],
        ['Construct actual zero occurrences with multiplicities and finite height cutoffs.',
         'Derive finite dyadic shells and their cardinality bounds from zero counts.',
         'Prove bounded-imaginary-strip Fourier decay and the exact transfer normalization.']),
    'ORDINATE-SIGN-AVERAGE-001': (
        ['tsum_eight_reflections', 'tsum_eight_reflections_pattern',
         'integral_occurrence_sum'],
        ['Construct the multiplicity-preserving occurrence involution from zeta symmetry.',
         'Prove the actual absolute Fourier-integral majorant and kernel coefficient bounds.']),
    'ORDINATE-CONSTANT-KERNEL-001': (
        ['evaluated_integrals_summable', 'evaluated_integrals_cutoff_limit',
         'tsum_eight_reflections'],
        ['Identify each evaluated Fourier integral with the reflected complex-test difference.',
         'Prove tuple decay, kernel replacement bounds and their support-dependent asymptotics.',
         'No interchange of the kernel-free infinite zero sum with the unevaluated Fourier integral is supplied.']),
}
SPECIAL_GAPS = {
    'PAIR-COUNT-001': ['Formalize inclusive endpoint counts, local unit-interval bounds and multiplicities; shell bounds are hypotheses only.'],
    'ORDINATE-COUNT-001': ['Prove the near and global weighted tuple counts from the recorded pair and unit counts; construct the unweighted shells needed for each application.'],
    'ORDINATE-ARGUMENT-VANISHING-001': ['Open research: the needed signed complex-argument error estimate is not proved.'],
    'ORDINATE-TRIPLE-001': ['Open research: the conventional ordinate-only asymptotic still requires a vanishing signed error.'],
}


def read(path):
    return (ROOT / path).read_text()


def derive():
    ledger = read('research/theorem-ledger.yaml')
    blocks = indexed_blocks(ledger)
    source_ids = set(indexed_blocks(ledger.split('\nclaims:\n', 1)[0]))
    deps, pending = {}, list(ROOTS)
    while pending:
        key = pending.pop()
        require(key in blocks, 'unknown ledger dependency: ' + key)
        if key in deps:
            continue
        deps[key] = [] if key in source_ids else id_list(field(blocks[key], 'dependencies'))
        pending.extend(deps[key])
    _, edges = closure('COVERAGE-ROOT', dict(deps, **{'COVERAGE-ROOT': ROOTS}))
    edges = [e for e in edges if e[0] != 'COVERAGE-ROOT']
    components = []
    for module in MODULES:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished or unapproved solution declaration: ' + path)
        for name in re.findall(r'^theorem (\w+)\b', source, re.M):
            components.append(dict(declaration='HigherCorrelations.' + name, source=path))
    names = [c['declaration'] for c in components]
    config = json.loads(read('lean/VerificationChallenges/summability.json'))
    require(len(names) == len(set(names)), 'duplicate solution declaration')
    require(config['theorem_names'] == names, 'challenge coverage differs from solution declarations')
    require(config['permitted_axioms'] == ['propext', 'Quot.sound', 'Classical.choice']
            and config['enable_nanoda'] is False, 'changed verification scope')
    axioms = re.findall(r'^#print axioms (\S+)$', read('lean/HigherCorrelations/AxiomReport.lean'), re.M)
    require(set(names) <= set(axioms) and len(axioms) == len(set(axioms)), 'axiom report coverage')
    nodes = []
    for key in sorted(deps):
        block = blocks[key]
        provenance = key in source_ids
        status = None if provenance else field(block, 'status')
        short, gaps = PARTIAL.get(key, ([], SPECIAL_GAPS.get(key, [
            'Formalize the exact recorded statement and proof, including its analytic hypotheses and limit order.'])))
        checked = ['HigherCorrelations.' + n for n in short]
        require(set(checked) <= set(names), 'unknown Lean component')
        scope = ('provenance' if provenance else 'open_research' if status == 'idea'
                 else 'partial' if checked else 'not_formalized')
        nodes.append(dict(id=key, dependencies=deps[key], ledger_status=status,
            ledger_block_sha256=hashlib.sha256(block.encode()).hexdigest(),
            source=None if provenance else flat_section(subsection(block, 'source')),
            coverage=scope, whole_claim_formalized=False, components=checked,
            remaining_obligations=[] if provenance else gaps))
    # A uses B: visit dependents before prerequisites, with deterministic tie-breaking.
    incoming = {k: 0 for k in deps}
    for _, b in edges:
        incoming[b] += 1
    order, ready = [], sorted(k for k, n in incoming.items() if n == 0)
    while ready:
        key = ready.pop(0)
        order.append(key)
        for dep in deps[key]:
            incoming[dep] -= 1
            if incoming[dep] == 0:
                ready.append(dep)
        ready.sort()
    require(len(order) == len(deps), 'dependency cycle')
    return dict(schema_version=1, task='formalization_coverage_bookkeeping',
        assumptions=['UNCONDITIONAL'], roots=ROOTS, analytic_proof_certificate=False,
        whole_graph_formalized=False, nodes=nodes, edges=edges,
        root_to_inputs_order=order, components=components,
        next_step='Construct the multiplicity-preserving zero-occurrence interface and finite height cutoffs, then discharge the counting and Fourier-decay hypotheses of ORDINATE-TRANSFER-001.')


def validate(record):
    require(record == derive(), 'stale or overstated analytic formalization coverage')


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.record = json.loads(RECORD.read_text())

    def test_current(self):
        validate(self.record)

    def test_missing_node(self):
        self.record['nodes'].pop()
        with self.assertRaises(ValueError): validate(self.record)

    def test_missing_edge(self):
        self.record['edges'].pop()
        with self.assertRaises(ValueError): validate(self.record)

    def test_false_promotion(self):
        self.record['nodes'][0]['whole_claim_formalized'] = True
        with self.assertRaises(ValueError): validate(self.record)

    def test_unknown_component(self):
        self.record['components'][0]['declaration'] = 'HigherCorrelations.notProved'
        with self.assertRaises(ValueError): validate(self.record)

    def test_stale_statement(self):
        self.record['nodes'][0]['ledger_block_sha256'] = '0' * 64
        with self.assertRaises(ValueError): validate(self.record)

    def test_open_research_preserved(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'ORDINATE-ARGUMENT-VANISHING-001')
        self.assertEqual(node['coverage'], 'open_research')
        node['coverage'] = 'partial'
        with self.assertRaises(ValueError): validate(self.record)

    def test_prerequisite_order(self):
        order = {k: i for i, k in enumerate(self.record['root_to_inputs_order'])}
        for a, b in self.record['edges']:
            self.assertLess(order[a], order[b])


if __name__ == '__main__':
    unittest.main()
