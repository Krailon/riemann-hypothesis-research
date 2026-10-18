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
         'ORDINATE-TRIPLE-001', 'PAIR-RHS-MEAN-001']
MODULES = ['OccurrenceSummability', 'OccurrenceLimits',
           'OccurrenceIntegration', 'SummabilityExamples']
COMPLETE_STATEMENTS = {'PAIR-EF-001', 'PAIR-MEANVALUE-001', 'PAIR-PRIME-COUNT-001'}
PARTIAL = {
    'PAIR-RHS-MEAN-001': (
        ['pairRHSMean_uniform', 'pairRHS_decomposition', 'pairRHSSquare_eq_zeroMeanSquare',
         'pairRHSSquare_integrable', 'pairZeroMeanSquare_integrable', 'pairRHSPrimeArchError_bound',
         'pairRHS_primeArch_interchange', 'pairRHS_coefficient_div_log_sum',
         'pairRHS_archError_L2', 'pairRHS_dsError_L2', 'pairRHS_pole_L2', 'pairRHS_trivial_L2',
         'pairRHSSmallError_bound', 'pairRHSLargeError_bound', 'pairRHSMean_zero_bound',
         'pairRHSMean_unit', 'pairRHSMean_top', 'pairRHSMean_minimal_height'],
        ['The full mean square, sharp mixed term, exact zero-series normalization and endpoints are checked with existential constants; the historical effective-constant assertion remains unformalized.']),

    'PAIR-PRIME-DIAGONAL-001': (
        ['pairMeanPrimeDiagonal_uniform', 'pairMeanPrimeDiagonal_split',
         'pairMeanPrimePowerDiagonal_sharp', 'pairMeanPrimePowerDiagonal_bounded',
         'pairDiagonal_cutoff_term', 'pairMeanPrimeDiagonal_unit'],
        ['The asymptotic, proper-power bound and endpoints are checked with existential constants; the historical effective-constant assertion remains unformalized.']),
    'PRIME-PNT-001': (
        ['pairDiagonalPNT_log_error', 'pairDiagonalCumulative_bound'],
        ['A sufficient global psi remainder follows from the pinned unconditional StrongPNT proof. The historical theta statement and effective constants remain separate obligations.']),
    'PAIR-PRIME-COUNT-001': (
        ['pairSieveNearby_bound', 'pairMeanPrimeNearby_bound', 'pairMeanPrimeNearby_uniform'], []),
    'PRIME-SIEVE-001': (
        ['pairSieve_prime_bound', 'pairSieveBadFactor_sum_le'],
        ['A uniform even-shift bound with an alternative averaged divisor factor is checked; the historical precise singular factor is not formalized.']),
    'PAIR-MEANVALUE-001': (
        ['pairMeanValue_explicit', 'pairMeanEnvelope_sandwich', 'pairMeanEnvelope_mass',
         'pairMeanEnvelope_fourier_zero', 'pairMeanWeighted_square_identity',
         'pairMeanWeighted_offdiag_bound', 'pairMeanPrime_meanvalue'], []),
    'PAIR-PRIME-MEAN-001': (
        ['pairMeanPrime_meanvalue', 'pairMeanPrimeCoefficient_summable',
         'pairMeanPrimeCoefficient_sqrt', 'pairMeanPrimeFrequency_cutoff', 'pairMeanPrimeNearby_bound',
         'pairMeanPrimeDiagonal_asymptotic', 'pairMeanPrimeDiagonal_upper',
         'pairPrimeMean_uniform', 'pairPrimeMean_decomposition', 'pairPrimeMean_combined_bound',
         'pairPrimeMeanBandwidth_admissible', 'pairPrimeMeanL2Norm_bound'],
        ['The Fourier mean-value input and actual prime-series specialization are checked.',
         'The optimized mean-square error, diagonal error and L2 bound are checked with existential constants. The historical effective-constant assertion remains unformalized.']),
    'PAIR-EF-001': (
        ['pairUniform_formula', 'pairUniform_named_bounds', 'pairUniform_remainder_bound',
         'pairUniform_endpoint', 'pairUniform_zero_height', 'pairDSConstant_approximation'], []),
    'GAMMA-DIGAMMA-001': (
        ['pairDigamma_remainder_bound'],
        ['The effective bound 2/|z| on Re(z)>0 is checked; the full historical fixed-sector assertion remains unformalized.']),
    'PAIR-EF-EXACT-001': (
        ['pairExact_formula', 'pairExact_endpoint', 'pairExact_interior',
         'pairContour_finite_rectangle', 'pairContour_candidate_residue_sum',
         'pairRectangle_height_tendsto', 'pairContour_left_tendsto',
         'pairRightIntegral_prime_identity', 'pairTrivialCorrection_continuous'],
        ['The exact identity and X=1 endpoint are checked in a separate formalized entry.',
         'The historical sharper contour bounds and effective-constant claims are not supplied by this alternative Hadamard bound.']),
    'ZETA-CONTOUR-001': (
        ['pairGoodHeight_sequence', 'pairZeta_goodHeight_power', 'pairContour_horizontal_tendsto'],
        ['Good heights and horizontal vanishing are checked using the coarser O(H^(7/4)) logarithmic-derivative envelope.',
         'The historical O(log^2 H) logarithmic-derivative bound remains unformalized.']),
    'PAIR-EF-MELLIN-001': (
        ['pairedMellinSeed_transform', 'pairedMellinIntegrand_bound',
         'pairedMellin_upward_integrable', 'pairedMellin_upward_normalization',
         'pairedMellin_truncation_limit', 'pairedMellinKernel_gt_one',
         'pairedMellinKernel_le_one', 'pairedMellinKernel_at_one', 'pairedMellin_kernel'],
        ['The full kernel identity, absolute convergence, normalization and endpoint are checked by Mellin inversion.',
         'The historical contour-shift proof and its two-parameter limit order are not formalized; the exact statement has a separate formalized entry.']),
    'PAIR-EF-CONVERGENCE-001': (
        ['pairZeroTerm_summable', 'pairPrimeTerm_summable', 'pairZero_locallyUniform',
         'pairPrime_locallyUniform', 'pairZeroSeries_continuous', 'pairPrimeSeries_continuous',
         'pairZero_cutoff_uniform', 'pairZero_cutoff_locallyUniform', 'pairZeroTail_bound',
         'pairZero_cutoff_error', 'pairSeries_convergence', 'pairPrimeTerm_at_knot', 'pairZeroTerm_at_one'],
        ['Convergence, continuity, endpoint conventions and the quantitative tail are checked with an existential absolute constant.',
         'The historical effective-constant assertion is not supplied by the unevaluated low-height count.']),
    'TRIPLE-SMOOTHED-CORRELATION-001': (
        ['triple_cutoff_limit', 'dominated_occurrence_limit', 'project_actual_summable_norm',
         'actualRationalKernel_bound', 'rationalTransferTerm_summable', 'rationalTransferSum_cutoff_limit',
         'actualRationalKernel_integral', 'actualProfile_integrable', 'actual_kernel_uniform_bounds'],
        [
         'Formalize the stated main term and named errors; the new real-test global majorants do not evaluate the complex-test errors.']),
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
         'actual_rational_transfer_scaled_anchor', 'actualRationalKernel_integral',
         'transferCoefficient_mass_bound', 'ordinateCoefficient_mass_bound'],
        ['The fixed-height rational transfer and its integral-profile identification are checked as separate components.',
         'Uniform real-test majorants and transfer coefficient bounds are now checked separately; a vanishing signed error remains open.']),
    'ORDINATE-SIGN-AVERAGE-001': (
        ['zeroMultiplicity_horizontalReflection', 'occurrenceReflection_involutive',
         'occurrenceReflection_ordinate', 'occurrenceReflection_displacement',
         'actual_eight_reflections', 'actual_signed_eight_reflections', 'actual_reflection_preserves_patterns',
         'integral_occurrence_sum'],
        ['Prove the actual absolute Fourier-integral majorant and kernel coefficient bounds.']),
    'ORDINATE-CONSTANT-KERNEL-001': (
        ['evaluated_integrals_summable', 'evaluated_integrals_cutoff_limit',
         'complexFourier_eq_inverse', 'actual_anchored_tail', 'actual_signed_eight_reflections',
         'actualProfile_symmetric_second', 'actualProfile_symmetric_fourth',
         'actual_horizontal_uniform_bounds', 'anchored_decay_twentieth_tail'],
        ['Formalize the kernel replacement bounds and their support-dependent asymptotics.',
         'No interchange of the kernel-free infinite zero sum with the unevaluated Fourier integral is supplied.']),
    'PAIR-COUNT-001': (
        ['zeroMultiplicity_pos', 'occurrenceCutoff_card', 'occurrence_count_local', 'occurrence_count_interval', 'occurrence_count_logarithmic'],
        ['The local logarithmic and inclusive cumulative upper counts are checked with existential constants.',
         'Formalize Riemann-von Mangoldt, its main term, and exclusion of real strip zeros; numerical effectiveness is not supplied.']),
    'PAIR-COUNT-KERNEL-001': (
        ['zeroKernel_summable_bound', 'zeroKernelTail_summable_bound', 'zeroKernel_distant_bound',
         'zeroKernel_exterior_bound', 'zeroKernel_interior_bound'],
        ['All four rational ordinate-kernel inequalities are checked with absolute existential constants.',
         'The historical numerical-effectiveness claim is not supplied by the bounded-height bucket.']),
    'ORDINATE-COUNT-001': (
        ['project_anchored_count_uniform', 'project_weighted_mass_tail', 'anchored_decay_twentieth_tail'],
        ['The global T(log T)^3(1+R)^4 count, normalized O((log T)^2) mass and twentieth-order tail are checked.',
         'Formalize the pair-dependent near O(T(log T)^2 R^2) count and stronger normalized O(log T) mass.']),
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
    uniform = json.loads(read('research/lean-uniform-height-inventory.json'))
    found = []
    for module in uniform['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished uniform-height solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in uniform['components']],
            'uniform-height inventory differs from source declarations')
    uniform_config = json.loads(read('lean/VerificationChallenges/uniform-height.json'))
    require(uniform_config['theorem_names'] == [c['declaration'] for c in uniform['components'] if c['comparator_checked']],
            'uniform-height Comparator coverage differs from inventory')
    require(uniform_config['permitted_axioms'] == config['permitted_axioms']
            and uniform_config['enable_nanoda'] is False, 'changed uniform-height verification scope')
    components.extend(uniform['components'])
    names.extend(c['declaration'] for c in uniform['components'])
    pair = json.loads(read('research/lean-pair-series-inventory.json'))
    found = []
    for module in pair['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair-series solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in pair['components']],
            'pair-series inventory differs from source declarations')
    pair_config = json.loads(read('lean/VerificationChallenges/pair-series.json'))
    require(pair_config['theorem_names'] == [c['declaration'] for c in pair['components'] if c['comparator_checked']],
            'pair-series Comparator coverage differs from inventory')
    require(pair_config['permitted_axioms'] == config['permitted_axioms']
            and pair_config['enable_nanoda'] is False, 'changed pair-series verification scope')
    components.extend(pair['components'])
    names.extend(c['declaration'] for c in pair['components'])
    mellin = json.loads(read('research/lean-paired-mellin-inventory.json'))
    found = []
    for module in mellin['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished paired-mellin solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in mellin['components']],
            'paired-mellin inventory differs from source declarations')
    mellin_config = json.loads(read('lean/VerificationChallenges/paired-mellin.json'))
    require(mellin_config['theorem_names'] == [c['declaration'] for c in mellin['components'] if c['comparator_checked']],
            'paired-mellin Comparator coverage differs from inventory')
    require(mellin_config['permitted_axioms'] == config['permitted_axioms']
            and mellin_config['enable_nanoda'] is False, 'changed paired-mellin verification scope')
    components.extend(mellin['components'])
    names.extend(c['declaration'] for c in mellin['components'])
    exact = json.loads(read('research/lean-pair-exact-inventory.json'))
    found = []
    for module in exact['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair-exact solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in exact['components']],
            'pair-exact inventory differs from source declarations')
    exact_config = json.loads(read('lean/VerificationChallenges/pair-exact.json'))
    require(exact_config['theorem_names'] == [c['declaration'] for c in exact['components'] if c['comparator_checked']],
            'pair-exact Comparator coverage differs from inventory')
    require(exact_config['permitted_axioms'] == config['permitted_axioms']
            and exact_config['enable_nanoda'] is False, 'changed pair-exact verification scope')
    components.extend(exact['components'])
    names.extend(c['declaration'] for c in exact['components'])
    pair_uniform = json.loads(read('research/lean-pair-uniform-inventory.json'))
    found = []
    for module in pair_uniform['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair-uniform solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in pair_uniform['components']],
            'pair-uniform inventory differs from source declarations')
    pair_uniform_config = json.loads(read('lean/VerificationChallenges/pair-uniform.json'))
    require(pair_uniform_config['theorem_names'] == [c['declaration'] for c in pair_uniform['components'] if c['comparator_checked']],
            'pair-uniform Comparator coverage differs from inventory')
    require(pair_uniform_config['permitted_axioms'] == config['permitted_axioms']
            and pair_uniform_config['enable_nanoda'] is False, 'changed pair-uniform verification scope')
    components.extend(pair_uniform['components'])
    names.extend(c['declaration'] for c in pair_uniform['components'])
    meanvalue = json.loads(read('research/lean-pair-meanvalue-inventory.json'))
    found = []
    for module in meanvalue['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair-meanvalue solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in meanvalue['components']],
            'pair-meanvalue inventory differs from source declarations')
    meanvalue_config = json.loads(read('lean/VerificationChallenges/pair-meanvalue.json'))
    require(meanvalue_config['theorem_names'] == [c['declaration'] for c in meanvalue['components'] if c['comparator_checked']],
            'pair-meanvalue Comparator coverage differs from inventory')
    require(meanvalue_config['permitted_axioms'] == config['permitted_axioms']
            and meanvalue_config['enable_nanoda'] is False, 'changed pair-meanvalue verification scope')
    components.extend(meanvalue['components'])
    names.extend(c['declaration'] for c in meanvalue['components'])
    sieve = json.loads(read('research/lean-pair-sieve-inventory.json'))
    found = []
    for module in sieve['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair-sieve solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in sieve['components']],
            'pair-sieve inventory differs from source declarations')
    sieve_config = json.loads(read('lean/VerificationChallenges/pair-sieve.json'))
    require(sieve_config['theorem_names'] == [c['declaration'] for c in sieve['components'] if c['comparator_checked']],
            'pair-sieve Comparator coverage differs from inventory')
    require(sieve_config['permitted_axioms'] == config['permitted_axioms']
            and sieve_config['enable_nanoda'] is False, 'changed pair-sieve verification scope')
    components.extend(sieve['components'])
    names.extend(c['declaration'] for c in sieve['components'])
    diagonal = json.loads(read('research/lean-pair-diagonal-inventory.json'))
    found = []
    for module in diagonal['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair-diagonal solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in diagonal['components']],
            'pair-diagonal inventory differs from source declarations')
    diagonal_config = json.loads(read('lean/VerificationChallenges/pair-diagonal.json'))
    require(diagonal_config['theorem_names'] == [c['declaration'] for c in diagonal['components'] if c['comparator_checked']],
            'pair-diagonal Comparator coverage differs from inventory')
    require(diagonal_config['permitted_axioms'] == config['permitted_axioms']
            and diagonal_config['enable_nanoda'] is False, 'changed pair-diagonal verification scope')
    components.extend(diagonal['components'])
    names.extend(c['declaration'] for c in diagonal['components'])
    prime_mean = json.loads(read('research/lean-pair-prime-mean-inventory.json'))
    found = []
    for module in prime_mean['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair-prime-mean solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in prime_mean['components']],
            'pair-prime-mean inventory differs from source declarations')
    prime_mean_config = json.loads(read('lean/VerificationChallenges/pair-prime-mean.json'))
    require(prime_mean_config['theorem_names'] == [c['declaration'] for c in prime_mean['components'] if c['comparator_checked']],
            'pair-prime-mean Comparator coverage differs from inventory')
    require(prime_mean_config['permitted_axioms'] == config['permitted_axioms']
            and prime_mean_config['enable_nanoda'] is False, 'changed pair-prime-mean verification scope')
    components.extend(prime_mean['components'])
    names.extend(c['declaration'] for c in prime_mean['components'])
    rhs_mean = json.loads(read('research/lean-pair-rhs-mean-inventory.json'))
    found = []
    for module in rhs_mean['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair-rhs-mean solution: ' + path)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)\b', source, re.M):
            found.append(dict(declaration='HigherCorrelations.' + name, source=path))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in rhs_mean['components']],
            'pair-rhs-mean inventory differs from source declarations')
    rhs_mean_config = json.loads(read('lean/VerificationChallenges/pair-rhs-mean.json'))
    require(rhs_mean_config['theorem_names'] == [c['declaration'] for c in rhs_mean['components'] if c['comparator_checked']],
            'pair-rhs-mean Comparator coverage differs from inventory')
    require(rhs_mean_config['permitted_axioms'] == config['permitted_axioms']
            and rhs_mean_config['enable_nanoda'] is False, 'changed pair-rhs-mean verification scope')
    components.extend(rhs_mean['components'])
    names.extend(c['declaration'] for c in rhs_mean['components'])
    require(len(names) == len(set(names)), 'duplicate cross-milestone declaration')
    axioms = re.findall(r'^#print axioms (\S+)$', read('lean/HigherCorrelations/AxiomReport.lean'), re.M)
    require(set(names + actual['imported_axioms'] + profile['imported_axioms'] + uniform['imported_axioms'] + pair['imported_axioms'] + mellin['imported_axioms'] + exact['imported_axioms'] + pair_uniform['imported_axioms'] + meanvalue['imported_axioms'] + sieve['imported_axioms'] + diagonal['imported_axioms'] + prime_mean['imported_axioms'] + rhs_mean['imported_axioms']) <= set(axioms) and len(axioms) == len(set(axioms)), 'axiom report coverage')
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
                 else 'formalized' if key in COMPLETE_STATEMENTS else 'partial' if checked else 'not_formalized')
        nodes.append(dict(id=key, dependencies=deps[key], ledger_status=status,
            ledger_block_sha256=hashlib.sha256(block.encode()).hexdigest(),
            source=None if provenance else flat_section(subsection(block, 'source')),
            coverage=scope, whole_claim_formalized=key in COMPLETE_STATEMENTS, components=checked,
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
        next_step='Assemble the normalized pair-correlation asymptotic from the checked RHS mean square and the zero-side comparison. The diagonal, prime mean-square and full RHS constants are existential; their effectivity remains separate. The sharper near count, full Riemann-von Mangoldt and signed o(1) remain open.')


def validate(record):
    require(record == derive(), 'stale or overstated analytic formalization coverage')


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.record = json.loads(RECORD.read_text())

    def test_current(self):
        validate(self.record)

    def test_meanvalue_complete_arithmetic_partial(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-MEANVALUE-001')
        self.assertTrue(node['whole_claim_formalized'])
        self.assertEqual(node['remaining_obligations'], [])
        prime = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-PRIME-MEAN-001')
        self.assertFalse(prime['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.pairMeanPrime_meanvalue', prime['components'])
        self.assertIn('HigherCorrelations.pairMeanPrimeDiagonal_asymptotic', prime['components'])
        self.assertIn('HigherCorrelations.pairPrimeMean_uniform', prime['components'])
        self.assertTrue(any('effective-constant' in gap for gap in prime['remaining_obligations']))

    def test_prime_mean_effectivity_and_rhs_scope(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-PRIME-MEAN-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.pairPrimeMeanL2Norm_bound', node['components'])
        self.assertIn('HigherCorrelations.pairPrimeMeanBandwidth_admissible', node['components'])
        self.assertNotIn('PAIR-RHS-MEAN-001', COMPLETE_STATEMENTS)
        rhs = indexed_blocks(read('research/theorem-ledger.yaml'))['PAIR-RHS-MEAN-001']
        self.assertEqual(field(rhs, 'status'), 'proved-draft')

    def test_rhs_effectivity_and_normalization(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-RHS-MEAN-001')
        self.assertIn('PAIR-RHS-MEAN-001', self.record['roots'])
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertTrue(any('effective-constant' in gap for gap in node['remaining_obligations']))
        for name in ['pairRHSMean_uniform', 'pairRHSSquare_eq_zeroMeanSquare',
                     'pairRHSPrimeArchError_bound', 'pairRHS_primeArch_interchange',
                     'pairRHSSmallError_bound', 'pairRHSLargeError_bound']:
            self.assertIn('HigherCorrelations.' + name, node['components'])
        claim = indexed_blocks(read('research/theorem-ledger.yaml'))['PAIR-RHS-MEAN-FORMAL-001']
        self.assertEqual(field(claim, 'status'), 'formalized')
        self.assertEqual(field(claim, 'constants_effective'), 'false')

    def test_rhs_remainders_and_endpoints(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-RHS-MEAN-001')
        for name in ['pairRHS_archError_L2', 'pairRHS_dsError_L2', 'pairRHS_pole_L2',
                     'pairRHS_trivial_L2', 'pairRHSMean_unit', 'pairRHSMean_top',
                     'pairRHSMean_minimal_height']:
            self.assertIn('HigherCorrelations.' + name, node['components'])

    def test_rhs_comparator_scope_drift(self):
        component = next(c for c in self.record['components']
                         if c['declaration'] == 'HigherCorrelations.pairRHSMean_uniform')
        component['comparator_checked'] = False
        with self.assertRaises(ValueError): validate(self.record)

    def test_prime_mean_comparator_scope_drift(self):
        component = next(c for c in self.record['components']
                         if c['declaration'] == 'HigherCorrelations.pairPrimeMean_uniform')
        component['comparator_checked'] = False
        with self.assertRaises(ValueError): validate(self.record)

    def test_diagonal_effectivity_remains_partial(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-PRIME-DIAGONAL-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.pairMeanPrimeDiagonal_uniform', node['components'])
        self.assertTrue(any('effective-constant' in gap for gap in node['remaining_obligations']))
        pnt = next(n for n in self.record['nodes'] if n['id'] == 'PRIME-PNT-001')
        self.assertFalse(pnt['whole_claim_formalized'])
        self.assertTrue(any('theta' in gap for gap in pnt['remaining_obligations']))

    def test_diagonal_comparator_scope_drift(self):
        component = next(c for c in self.record['components']
                         if c['declaration'] == 'HigherCorrelations.pairMeanPrimeDiagonal_uniform')
        component['comparator_checked'] = False
        with self.assertRaises(ValueError): validate(self.record)

    def test_sieve_complete_precise_singular_factor_partial(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-PRIME-COUNT-001')
        self.assertTrue(node['whole_claim_formalized'])
        self.assertEqual(node['remaining_obligations'], [])
        sieve = next(n for n in self.record['nodes'] if n['id'] == 'PRIME-SIEVE-001')
        self.assertFalse(sieve['whole_claim_formalized'])
        self.assertTrue(any('singular factor' in gap for gap in sieve['remaining_obligations']))

    def test_sieve_comparator_scope_drift(self):
        component = next(c for c in self.record['components']
                         if c['declaration'] == 'HigherCorrelations.pairMeanPrimeNearby_bound')
        component['comparator_checked'] = False
        with self.assertRaises(ValueError): validate(self.record)

    def test_meanvalue_comparator_scope_drift(self):
        component = next(c for c in self.record['components']
                         if c['declaration'] == 'HigherCorrelations.pairMeanValue_explicit')
        component['comparator_checked'] = False
        with self.assertRaises(ValueError): validate(self.record)

    def test_pair_convergence_effectiveness_remains_partial(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-EF-CONVERGENCE-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.pairZero_cutoff_error', node['components'])
        self.assertTrue(any('effective-constant' in gap for gap in node['remaining_obligations']))

    def test_mellin_statement_and_proof_route(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-EF-MELLIN-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertIn('HigherCorrelations.pairedMellinKernel_at_one', node['components'])
        self.assertIn('HigherCorrelations.pairedMellin_kernel', node['components'])
        self.assertTrue(any('contour-shift' in gap for gap in node['remaining_obligations']))

    def test_exact_identity_preserves_historical_contour_scope(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-EF-EXACT-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertIn('HigherCorrelations.pairExact_formula', node['components'])
        self.assertIn('HigherCorrelations.pairExact_endpoint', node['components'])
        self.assertTrue(any('sharper contour' in gap for gap in node['remaining_obligations']))
        contour = next(n for n in self.record['nodes'] if n['id'] == 'ZETA-CONTOUR-001')
        self.assertFalse(contour['whole_claim_formalized'])
        self.assertTrue(any('O(log^2 H)' in gap for gap in contour['remaining_obligations']))

    def test_missing_node(self):
        self.record['nodes'].pop()
        with self.assertRaises(ValueError): validate(self.record)

    def test_missing_edge(self):
        self.record['edges'].pop()
        with self.assertRaises(ValueError): validate(self.record)

    def test_uniform_pair_statement_and_gamma_scope(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-EF-001')
        self.assertEqual(node['coverage'], 'formalized')
        self.assertTrue(node['whole_claim_formalized'])
        self.assertEqual(node['remaining_obligations'], [])
        self.assertIn('HigherCorrelations.pairUniform_named_bounds', node['components'])
        gamma = next(n for n in self.record['nodes'] if n['id'] == 'GAMMA-DIGAMMA-001')
        self.assertEqual(gamma['coverage'], 'partial')
        self.assertFalse(gamma['whole_claim_formalized'])
        self.assertTrue(any('fixed-sector' in gap for gap in gamma['remaining_obligations']))

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
        self.assertTrue(any('Riemann-von Mangoldt' in gap for gap in node['remaining_obligations']))

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

    def test_uniform_components_recorded(self):
        count = next(n for n in self.record['nodes'] if n['id'] == 'ORDINATE-COUNT-001')
        self.assertIn('HigherCorrelations.project_anchored_count_uniform', count['components'])
        self.assertIn('HigherCorrelations.anchored_decay_twentieth_tail', count['components'])
        self.assertFalse(count['whole_claim_formalized'])
        self.assertTrue(any('pair-dependent' in gap for gap in count['remaining_obligations']))

    def test_kernel_constants_scope(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-COUNT-KERNEL-001')
        self.assertIn('HigherCorrelations.zeroKernel_interior_bound', node['components'])
        self.assertTrue(any('existential constants' in gap for gap in node['remaining_obligations']))
        self.assertFalse(node['whole_claim_formalized'])

    def test_uniform_comparator_scope_drift(self):
        component = next(c for c in self.record['components']
                         if c['declaration'] == 'HigherCorrelations.occurrence_count_local')
        component['comparator_checked'] = False
        with self.assertRaises(ValueError): validate(self.record)

    def test_prerequisite_order(self):
        order = {k: i for i, k in enumerate(self.record['root_to_inputs_order'])}
        for a, b in self.record['edges']:
            self.assertLess(order[a], order[b])


if __name__ == '__main__':
    unittest.main()
