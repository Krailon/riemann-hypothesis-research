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
        ['triple_cutoff_limit', 'dominated_occurrence_limit', 'project_actual_summable_norm',
         'actualRationalKernel_bound', 'rationalTransferTerm_summable', 'rationalTransferSum_cutoff_limit',
         'actualRationalKernel_integral', 'actualProfile_integrable'],
        [
         'Formalize the stated main term and named errors; no uniform height majorant is supplied.']),
    'TRIPLE-MASTER-001': (
        ['integral_occurrence_sum', 'integral_occurrence_cutoff_limit', 'actualProfile_integrable'],
        ['Prove the uniform master-kernel summable integral-norm bound.',
         'Formalize the explicit-formula expansion, prime-side sums and normalization.']),
    'TRIPLE-KERNEL-PROFILE-001': (
        ['dominated_integral_limit', 'rational_denominator_lower', 'rational_denominator_ne_zero',
         'rationalKernel_reciprocal', 'rationalProfile_bound', 'rationalProfile_swap',
         'rationalProfile_conj', 'rationalProfile_coincident', 'rationalProfile_real',
         'profileIntegrand_bound', 'profileIntegrand_integrable', 'integralProfile_eq',
         'integralProfile_continuous_gaps', 'integralProfile_contDiffAt',
         'horizontalPartial_eq_profileJet', 'horizontalPartial_bound', 'profileRay_derivative_bound',
         'profile_symmetric_second_bound', 'profile_symmetric_fourth_bound'],
        ['The profile identity, collisions, endpoints, smoothness and horizontal derivatives are checked by the listed components.',
         'The historical contour-residue proof route and its TRIPLE-MASTER-001 dependency are not formalized; the checked identity uses finite-interval partial fractions.']),
    'ORDINATE-TRANSFER-001': (
        ['occurrence_height_finite', 'mem_occurrenceCutoff', 'occurrenceCutoff_exhausts',
         'zero_occurrences_countable', 'occurrence_count_polynomial', 'actual_shell_cardinality',
         'complexFourier_eq_inverse', 'complexFourier_strip_decay', 'actual_summable_norm',
         'actual_signed_difference_summable', 'actual_independent_cutoff_limit', 'actual_signed_cutoff_limit',
         'rationalTransferTerm_summable', 'rationalTransferSum_cutoff_limit',
         'rationalTransfer_finite_telescope', 'rationalTransfer_tsum_telescope',
         'transfer_normalization', 'actual_rational_transfer', 'actual_rational_transfer_benchmark',
         'actual_rational_transfer_scaled_anchor', 'actualRationalKernel_integral'],
        ['The fixed-height rational transfer and its integral-profile identification are checked as separate components.',
         'No uniform height asymptotics or vanishing error estimate follows from this fixed-height identity.']),
    'ORDINATE-SIGN-AVERAGE-001': (
        ['zeroMultiplicity_horizontalReflection', 'occurrenceReflection_involutive',
         'occurrenceReflection_ordinate', 'occurrenceReflection_displacement',
         'actual_eight_reflections', 'actual_signed_eight_reflections', 'actual_reflection_preserves_patterns',
         'integral_occurrence_sum'],
        ['Prove the actual absolute Fourier-integral majorant and kernel coefficient bounds.']),
    'ORDINATE-CONSTANT-KERNEL-001': (
        ['evaluated_integrals_summable', 'evaluated_integrals_cutoff_limit',
         'complexFourier_eq_inverse', 'actual_anchored_tail', 'actual_signed_eight_reflections',
         'actualProfile_symmetric_second', 'actualProfile_symmetric_fourth'],
        ['Formalize the kernel replacement bounds and their support-dependent asymptotics.',
         'No interchange of the kernel-free infinite zero sum with the unevaluated Fourier integral is supplied.']),
    'PAIR-COUNT-001': (
        ['zeroMultiplicity_pos', 'occurrenceCutoff_card', 'occurrence_count_polynomial'],
        ['The formalized all-sign inclusive polynomial bound is weaker than this ledger claim.',
         'Formalize Riemann-von Mangoldt, the local logarithmic unit-interval bound, and exclusion of real strip zeros.']),
    'ORDINATE-COUNT-001': (
        ['actual_shell_cardinality', 'actual_anchored_tail'],
        ['Prove the near and global weighted counts with the recorded uniform T dependence from the pair and unit counts.']),
}
SPECIAL_GAPS = {
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
    generic_names = [c['declaration'] for c in components]
    names = list(generic_names)
    config = json.loads(read('lean/VerificationChallenges/summability.json'))
    require(len(names) == len(set(names)), 'duplicate solution declaration')
    require(config['theorem_names'] == generic_names, 'challenge coverage differs from solution declarations')
    require(config['permitted_axioms'] == ['propext', 'Quot.sound', 'Classical.choice']
            and config['enable_nanoda'] is False, 'changed verification scope')
    actual = json.loads(read('research/lean-actual-occurrences-inventory.json'))
    found = []
    for module in actual['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished actual-occurrence solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in actual['components']],
            'actual-occurrence inventory differs from source declarations')
    actual_config = json.loads(read('lean/VerificationChallenges/actual-occurrences.json'))
    require(actual_config['theorem_names'] == [c['declaration'] for c in actual['components'] if c['comparator_checked']],
            'actual-occurrence Comparator coverage differs from inventory')
    require(actual_config['permitted_axioms'] == config['permitted_axioms']
            and actual_config['enable_nanoda'] is False, 'changed actual-occurrence verification scope')
    components.extend(actual['components'])
    names.extend(c['declaration'] for c in actual['components'])
    rational = json.loads(read('research/lean-rational-transfer-inventory.json'))
    found = []
    for module in rational['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished rational-transfer solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in rational['components']],
            'rational-transfer inventory differs from source declarations')
    rational_config = json.loads(read('lean/VerificationChallenges/rational-transfer.json'))
    require(rational_config['theorem_names'] == [c['declaration'] for c in rational['components'] if c['comparator_checked']],
            'rational-transfer Comparator coverage differs from inventory')
    require(rational_config['permitted_axioms'] == config['permitted_axioms']
            and rational_config['enable_nanoda'] is False, 'changed rational-transfer verification scope')
    components.extend(rational['components'])
    names.extend(c['declaration'] for c in rational['components'])
    profile = json.loads(read('research/lean-integral-profile-inventory.json'))
    found = []
    for module in profile['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished integral-profile solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in profile['components']],
            'integral-profile inventory differs from source declarations')
    profile_config = json.loads(read('lean/VerificationChallenges/integral-profile.json'))
    require(profile_config['theorem_names'] == [c['declaration'] for c in profile['components'] if c['comparator_checked']],
            'integral-profile Comparator coverage differs from inventory')
    require(profile_config['permitted_axioms'] == config['permitted_axioms']
            and profile_config['enable_nanoda'] is False, 'changed integral-profile verification scope')
    components.extend(profile['components'])
    names.extend(c['declaration'] for c in profile['components'])
    require(len(names) == len(set(names)), 'duplicate cross-milestone declaration')
    axioms = re.findall(r'^#print axioms (\S+)$', read('lean/HigherCorrelations/AxiomReport.lean'), re.M)
    require(set(names + actual['imported_axioms'] + profile['imported_axioms']) <= set(axioms) and len(axioms) == len(set(axioms)), 'axiom report coverage')
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
        next_step='Prove the sharper local counts and uniform height estimates, then work through the explicit-formula dependency graph. The integral profile and horizontal derivatives are checked; the signed o(1) remains open.')


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

    def test_comparator_scope_drift(self):
        component = next(c for c in self.record['components'] if 'comparator_checked' in c)
        component['comparator_checked'] = not component['comparator_checked']
        with self.assertRaises(ValueError): validate(self.record)

    def test_stronger_count_remains_partial(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-COUNT-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertTrue(any('local logarithmic' in gap for gap in node['remaining_obligations']))

    def test_profile_components_do_not_promote_historical_graph(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'ORDINATE-TRANSFER-001')
        self.assertIn('HigherCorrelations.actual_rational_transfer', node['components'])
        self.assertFalse(node['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.actualRationalKernel_integral', node['components'])
        profile = next(n for n in self.record['nodes'] if n['id'] == 'TRIPLE-KERNEL-PROFILE-001')
        self.assertFalse(profile['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.integralProfile_eq', profile['components'])
        self.assertIn('HigherCorrelations.horizontalPartial_bound', profile['components'])
        self.assertTrue(any('TRIPLE-MASTER-001' in gap for gap in profile['remaining_obligations']))

    def test_rational_comparator_scope_drift(self):
        component = next(c for c in self.record['components']
                         if c['declaration'] == 'HigherCorrelations.actual_rational_transfer')
        component['comparator_checked'] = False
        with self.assertRaises(ValueError): validate(self.record)

    def test_profile_comparator_scope_drift(self):
        component = next(c for c in self.record['components']
                         if c['declaration'] == 'HigherCorrelations.integralProfile_eq')
        component['comparator_checked'] = False
        with self.assertRaises(ValueError): validate(self.record)

    def test_prerequisite_order(self):
        order = {k: i for i, k in enumerate(self.record['root_to_inputs_order'])}
        for a, b in self.record['edges']:
            self.assertLess(order[a], order[b])


if __name__ == '__main__':
    unittest.main()
