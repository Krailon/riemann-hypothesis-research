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
         'ORDINATE-TRIPLE-001', 'PAIR-RHS-MEAN-001', 'PAIR-TRUNC-001', 'PAIR-COMPARE-001', 'PAIR-ASYMPTOTIC-001', 'PAIR-TRANSLATION-001']
MODULES = ['OccurrenceSummability', 'OccurrenceLimits',
           'OccurrenceIntegration', 'SummabilityExamples']
COMPLETE_STATEMENTS = {'TRIPLE-LOG-GAP-001', 'PAIR-EF-001', 'PAIR-MEANVALUE-001', 'PAIR-PRIME-COUNT-001', 'PAIR-POSITIVITY-001', 'PAIR-TRANSLATION-001', 'TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001', 'TRIPLE-SINE-MEASURE-001'}
PARTIAL = {
    'ORDINATE-DENSITY-INPUT-001': (['mem_rightDensityWindow', 'mem_leftDensityWindow', 'mem_horizontalDensityWindow', 'mem_rightDensityInterval', 'mem_leftDensityInterval', 'mem_horizontalDensityInterval', 'rightDensityWindow_empty', 'horizontalDensityWindow_empty', 'horizontalDensityInterval_empty', 'rightDensityWindow_mono', 'horizontalDensityInterval_mono', 'rightDensityWindow_card', 'horizontalDensityInterval_card', 'rightDensityInterval_endpoint', 'horizontalDensityInterval_endpoint', 'rightDensityCount_split', 'rightDensityCount_difference', 'densityWindow_reflection', 'densityInterval_reflection', 'horizontalDensityWindow_twice_right', 'horizontalDensityInterval_twice_right', 'horizontalDensityInterval_excludes_boundary', 'horizontalDensityInterval_excludes_line', 'leftDensityWindow_empty', 'rightDensityInterval_empty', 'leftDensityInterval_empty', 'mem_horizontalDensityInterval_singleton', 'rightDensityCount_card', 'densityInterval_dyadic_cover', 'density_comparable_interval', 'density_power_exp', 'density_scaled_tail_bound', 'density_scaled_tail_antitone', 'density_scaled_tail_endpoint', 'density_scaled_tail_frozen', 'littlewoodSegmentLog_start', 'littlewoodSegmentLog_deriv', 'littlewoodSegmentLog_exp', 'littlewoodSegmentLog_re', 'littlewood_affine_integral', 'littlewood_integral_re', 'littlewood_integral_im', 'LittlewoodRectangle.horizontal', 'LittlewoodRectangle.vertical', 'littlewoodBottomLog_deriv', 'littlewoodRightLog_deriv', 'littlewoodTopLog_deriv', 'littlewoodBottomLog_exp', 'littlewoodRightLog_exp', 'littlewoodTopLog_exp', 'LittlewoodRectangle.horizontal_logDeriv', 'LittlewoodRectangle.vertical_logDeriv', 'littlewoodLog_re_of_exp', 'littlewood_vertical_log_integrable', 'littlewood_arguments_integrable', 'littlewood_boundary_integral', 'littlewood_zero_set_exists', 'littlewood_weighted_argument', 'littlewood_identity', 'littlewood_mass_count', 'littlewood_count_bound', 'littlewood_count_of_budget', 'littlewood_boundary_branch_invariant', 'littlewood_count_threshold', 'littlewood_zeta_count', 'littlewood_zeta_bound', 'littlewood_zeta_of_budget', 'littlewood_zeta_rectangle', 'littlewood_zeta_budget_positive_height', 'littlewood_constant_boundary', 'littlewood_repeated_zero'], ['Finite counts and reflection/window adapters are checked. Littlewood transported logarithms, integrability, exact rectangle identity, multiplicity-weighted count inequality and actual zeta specialization are now checked on zero-free boundaries. Window and scaled-tail bounds still require the explicit UniformDyadicDensity hypothesis; its analytic proof, mollifier/second-moment estimates, boundary-zero limiting arguments and effective source constants remain unformalized. No close-pair bound, density moment or signed-error limit follows.']),
    'TRIPLE-MAIN-TERM-COMPARISON-001': (['mainTermFrequencyTest_apply', 'mainTermPhysicalTest_apply', 'mainTermPhysicalTest_fourier', 'sineR2_reflection', 'sineR3_reflection', 'sineBenchmark_reflection', 'sineBenchmark_inverse_pairing', 'sineComplement_gauge', 'sineBenchmark_planar_zero', 'sineBenchmark_line_weight', 'sineBenchmark_trace_integrable', 'sineBenchmarkSpectrum_closed', 'mainTermBenchmark_closed', 'mainTermBenchmark_margin', 'mainTermComparison_exact', 'mainTermComparison_margin', 'mainTerm_signed_bound', 'mainTerm_frozen_bound', 'mainTerm_frozen_bound_deriv', 'mainTerm_signed_limit', 'mainTerm_frozen_limit', 'mainTerm_signed_compact_limit', 'mainTerm_frozen_compact_limit', 'mainTerm_signed_normalized_limit', 'mainTerm_frozen_normalized_limit', 'mainTermPhysicalTest_zero', 'mainTermBenchmark_zero', 'mainTerm_signed_normalized_compact_limit', 'mainTerm_frozen_normalized_compact_limit'], ['Exact benchmark identification, inherited uniform weighted bounds and fixed-test limits are checked. Numerical effectiveness of the inherited uniform constants remains uncertified; no ordinate-only or closed-boundary zeta theorem follows.']),
    'TRIPLE-SINE-MEASURE-001': (['sineOverlap_translated', 'sineOverlap_interval', 'sineOverlap_span', 'sineOverlap_volume', 'sineOverlap_length', 'sineOverlap_measurable', 'sineOverlap_finite', 'sineOverlapIntegrand_indicator', 'sineOverlapIntegrand_integrable', 'sineOverlap_integral', 'sineOverlap_nonempty', 'sineOverlap_touching', 'sineOverlap_empty', 'sineOverlap_length_pos', 'sineOverlap_length_zero', 'sineOverlap_length_sector', 'sineOverlap_length_axes', 'sineOverlap_length_origin', 'sineOverlap_length_repeated', 'sineOverlap_length_examples', 'sineCycle_continuous', 'sineCycle_bound', 'sineCycle_reflection', 'sineCycle_origin', 'sineCycle_axes', 'sineCycleDensity_bounds', 'sineCycleDensity_reflection', 'sineCycleDensity_continuous', 'sineCycleDensity_compactSupport', 'sineCycleDensity_integrable', 'sineDensityPlane_integrable', 'sineCyclePlane_weighted_integrable', 'sineDensityPlane_weighted_integrable', 'sineParameterIntegrand_majorant', 'sineParameterIntegrand_integrable', 'sineParameterIntegrand_fubini', 'sineParameterIntegrand_inner', 'sineInterval_character', 'sineParameterIntegrand_plane_integral', 'sineCycleDensity_inverse_integral', 'sineDensityPlane_inverse', 'sineDensityPlane_fourier', 'sineDensityPlane_mass', 'sineCycle_pairing', 'sineCycle_inverse_pairing', 'sineSquared_weighted_integrable', 'sineTriangle_weighted_integrable', 'sineSquared_pairing', 'sineSquared_inverse_pairing', 'sineLineCoords_antilipschitz', 'sineLineRestriction_apply', 'sineLine_integrable', 'sineSlice_measurePreserving', 'sineSlice_integral', 'sineSlice_dot', 'sineLine_dot', 'sineComplementRestriction_apply', 'sineComplement_integrable', 'sineMarginal_majorant', 'sineMarginal_continuous', 'sineMarginal_integrable', 'sineMarginal_fourier', 'sineSlice_fourier_marginal', 'sineLine_fourier_integral', 'sineDirection_dot', 'sineDirection_fourier_duality', 'sineDirection_square_pairing', 'sineDirection_triangle_pairing', 'sinePlane_weighted_integrable', 'sineLine_weighted_integrable', 'sinePlane_tempered', 'sineLine_tempered', 'sineSquare_bound', 'sineR2_continuous', 'sineR2_bound', 'sineR3_continuous', 'sineR3_bound', 'sineFourier_twice', 'sineDirection_triangle_reflection', 'sineDirection_plane_square_pairing', 'sineLine_square_fourier', 'sinePlane_square_fourier', 'sineLine_constant_fourier', 'sinePlane_constant_fourier', 'sineAtom_fourier', 'sineCycle_distribution_fourier', 'sineR3_determinant', 'sineCumulantDensity_closed', 'sineCumulantDensity_exterior', 'sineFactorialDensity_origin', 'sineCumulants_distinct', 'sineR3_factorial_identity', 'sineFactorialDensity_positive', 'sineDifferenceForm_continuous', 'sineLineForm_continuous', 'sineSquarePlane_integrable', 'sineTriangle_bound', 'sineTrianglePlane_integrable', 'sineLine_R2_expansion', 'sineComplement_m_expansion', 'sineR3_pairing_expansion', 'sineCumulantDensity_pairing_expansion', 'sineBenchmark_five', 'sineBenchmarkSpectrum_integrable', 'sineBenchmark_partial_fourier', 'sineBenchmark_distinct_fourier', 'sineBenchmarkRow_fourier', 'sineBenchmark_fourier', 'sineOrdinaryCumulant_fourier', 'sineFactorialCumulant_fourier', 'sineBenchmark_moment_cumulant', 'sineBenchmark_tempered', 'sineOrdinaryCumulant_tempered', 'sineFactorialCumulant_tempered', 'sineBenchmark_distribution_fourier', 'sineOrdinaryCumulant_distribution_fourier', 'sineFactorialCumulant_distribution_fourier', 'sineBenchmark_integrable', 'sineBenchmark_continuous', 'sineOrdinaryCumulant_continuous', 'sineFactorialCumulant_continuous', 'sineBenchmarkRow_tempered', 'sineCovarianceLift_tempered', 'sineBenchmark_distribution_moment_cumulant', 'sineBenchmark_manuscript'], []),
    'TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001': (['rationalProfile_origin', 'rationalProfile_real', 'profileGapFactor_denominator_ne', 'profileGapFactor_norm_bound', 'profileGapFactor_difference', 'profileReciprocalSum_difference', 'rationalProfile_eq_gap_factors', 'profileGapFactor_difference_bounded', 'rationalProfile_gap_bound', 'rationalProfile_scaled_gap_bound', 'microscopic_meanSpacing_ge_one', 'microscopic_meanSpacing_tendsto', 'rationalProfile_microscopic_bound', 'rationalProfile_microscopic_tendstoUniformlyOn', 'rationalProfile_microscopic_zero_gaps', 'rationalProfile_microscopic_zero_radius', 'rationalProfile_microscopic_coincident_gaps', 'rationalProfile_microscopic_closed_endpoints', 'criticalGapQuadratic_nonneg', 'criticalGapQuadratic_bound', 'criticalGapQuadratic_div', 'criticalProfileRemainderConstant_nonneg', 'rationalProfile_critical_remainder_identity', 'rationalProfile_critical_remainder_bound', 'rationalProfile_critical_scaled_bound', 'rationalProfile_critical_microscopic_bound', 'rationalProfile_critical_leading_bound', 'rationalProfile_critical_zero_radius', 'rationalProfile_critical_coincident_bound', 'rationalProfile_critical_scale_endpoint', 'rationalProfile_critical_height_endpoint', 'rationalProfile_critical_gap_endpoints', 'criticalMasterGap_unscale', 'tripleAnchoredProfile_critical_quadratic_bound', 'tripleAnchoredProfile_critical_leading_bound', 'tripleMasterKernel_critical_quadratic_bound', 'tripleMasterKernel_critical_leading_bound', 'tripleTestKernel_critical_quadratic_bound', 'tripleTestKernel_critical_leading_bound', 'tripleAnchoredProfile_critical_repeated', 'tripleMasterKernel_critical_zero_weight', 'zeroGapHorizontal_differences', 'zeroGapHorizontal_factor_bounds', 'zeroGapHorizontal_factor_pos', 'zeroGapHorizontal_factor_ne_zero', 'zeroGapHorizontalDenominator_bounds', 'zeroGapHorizontalDenominator_pos', 'zeroGapHorizontalDenominator_ne_zero', 'zeroGapHorizontal_numerator_lower', 'zeroGapHorizontalProfile_pos', 'rationalProfile_zero_gap_horizontal', 'zeroGapHorizontalProfile_swap', 'zeroGapHorizontalProfile_reflection', 'zeroGapHorizontalProfile_origin', 'zeroGapHorizontalProfile_cancelling', 'zeroGapHorizontalProfile_aligned', 'zeroGapHorizontalProfile_quarter', 'zeroGapHorizontalProfile_quarter_ne_origin', 'zeroGapHorizontalProfile_corners', 'rationalProfile_zero_gap_scaled_bound', 'rationalProfile_zero_gap_microscopic_bound', 'rationalProfile_zero_gap_tendstoUniformlyOn', 'criticalLocalNormalization_denominators', 'criticalLocalNormalization_identity', 'criticalLocalNormalization_complex', 'criticalLocalCoefficient_transferRatio', 'criticalLocalNormalization_transferCoefficient', 'criticalLocalCoefficient_sub_log', 'criticalLocalCoefficient_bounds', 'criticalLocalCoefficient_error', 'criticalLocalCoefficient_tendsto', 'criticalLocalCoefficient_complex_tendsto', 'criticalLocalCoefficient_endpoint', 'criticalLocalNormalization_endpoint_spacing', 'criticalLocalNormalization_endpoint_excluded'], []),
    'TRIPLE-KERNEL-LOCALIZATION-001': (['tripleAnchoredProfile_denominators', 'tripleMasterKernelIntegrand_translate', 'tripleAnchoredProfile_integrable', 'tripleAnchoredProfile_integral', 'tripleAnchoredProfile_test_order', 'tripleKernel_weighted_profile_integrable', 'tripleKernel_frozen_profile_integrable', 'tripleKernelLocalizationIntegrand_integrable', 'tripleKernelLocalizationError_absolutely_integrable', 'tripleMasterKernel_anchored_integral', 'tripleMasterKernel_localization', 'tripleTestKernel_localization', 'scalar_denominator_half_strip', 'scalarKernel_half_strip_bound', 'localization_pair_majorant_integrable', 'localization_pair_majorant_integral', 'localization_anchor_moment_bound', 'profileIntegrand_localization_moment', 'localization_weight_difference', 'tripleKernelLocalizationIntegrand_bound', 'tripleKernelLocalizationIntegrand_integrable_lipschitz', 'tripleKernelLocalizationError_bound', 'tripleKernelLocalizationError_bound_deriv', 'localizationRegion_measurable', 'localizationRegion_disjoint', 'localization_weight_zero', 'localizationErrorDensity_integrable', 'localizationRegionalDensity_integrable', 'localizationErrorDensity_integral', 'localizationRegionalDensity_partition', 'localizationRegionalError_partition', 'localizationRegionalMass_nonneg', 'localizationRegionalError_norm_le', 'localization_log_ge_one', 'localization_local_log', 'localization_unit_shell_weight', 'localization_near_moment_finite', 'localizationTailProfile_nonneg', 'localizationTailProfile_integrable', 'localization_tail_scaled_bound', 'localization_scaled_profile_integrable', 'localization_scaled_profile_integral', 'localizationAnchorWeight_nonneg', 'localizationRegionalDensity_majorant', 'localization_finite_product', 'localization_finite_majorant', 'localization_near_weight_zero', 'localization_near_anchor_sum', 'localization_far_center_anchor_sum', 'localization_Q_nonneg', 'localization_Q_local', 'localization_anchor_count', 'localization_mass_of_indicator_bound', 'localization_near_finite_mass', 'localization_far_center_finite_mass', 'localization_far_anchor_weight', 'localization_far_anchor_finite_mass', 'localizationRegionalMass_summable_of_finite', 'localizationRegionalError_summable_bound', 'localizationRegional_sum_integral', 'localization_near_summed_mass', 'localization_far_center_summed_mass', 'localization_far_anchor_summed_mass', 'localization_total_error_le_masses', 'tripleKernelLocalizationError_summed_bound', 'tripleKernelLocalizationError_summed_bound_deriv', 'tripleFrozenProfile_test_order', 'tripleFrozenProfile_eq_sub', 'tripleFrozenProfile_norm_le', 'tripleFrozen_weight_mass_bound', 'tripleFrozen_kernel_mass_bound', 'tripleFrozenProfile_summable_bound', 'tripleFrozenProfile_norm_summable', 'tripleFrozenProfile_mass_triangle', 'tripleFrozenProfile_summable_bound_deriv', 'tripleFrozenTestProfile_summable_bound', 'tripleFrozenProfile_sum_identity', 'tripleFrozenTestProfile_sum_identity', 'tripleFrozenProfile_independent_cutoff', 'tripleFrozenProfile_height_cutoff', 'tripleFrozenTestProfile_independent_cutoff', 'tripleFrozenProfile_zero', 'tripleFrozenProfile_repeated', 'signedTest_integrand_bound', 'signedTest_integrable', 'signedTest_bound', 'signedTest_weighted_summable_bound', 'tripleFrozenTestProfile_weighted_bound', 'tripleTestKernel_weighted_bound', 'tripleLocalizationError_weighted_bound', 'tripleFrozenTestProfile_weighted_summable', 'tripleFrozenTestProfile_weighted_independent_cutoff', 'tripleFrozenTestProfile_weighted_height_cutoff', 'tripleFrozenTestProfile_weighted_zero_test', 'tripleFrozenTestProfile_weighted_zero_weight', 'tripleFrozenTestProfile_weighted_repeated', 'frozenStatistic_profile_formula', 'frozenStatistic_transfer_identity', 'frozenStatistic_independent_cutoff', 'frozenStatistic_height_cutoff', 'frozenStatistic_zero_test', 'frozenStatistic_zero_weight', 'frozenTransferError_raw_bound', 'profileTransfer_power_scale', 'profileTransfer_height_bounds', 'profileTransfer_log_budget', 'frozenTransferError_bound', 'frozenStatistic_transfer_bound', 'frozenStatistic_transfer_bound_deriv', 'profileTransfer_envelope_tendsto', 'frozenTransferError_tendsto', 'frozenStatistic_transfer_tendsto', 'profileTransfer_smoothing_bounds', 'frozenStatistic_uniform_bound', 'frozenStatistic_fixed_margin_limit', 'frozenStatistic_compact_limit', 'tripleKernelLocalizationError_zero', 'tripleAnchoredProfile_repeated', 'tripleMasterKernel_localization_bound', 'tripleTestKernel_localization_bound', 'tripleKernelLocalizationError_equal_ordinates'], [
        'The exact decomposition, tuplewise and summed near/far bounds, and unweighted/complex-test weighted frozen-profile absolute summability with uniform mass bounds and independent fixed-height cutoffs are checked. Normalized correlation transfer, its separate error budget, and the fixed-test T-to-infinity limit are checked. Numerical effectiveness of inherited summed constants is not certified; they remain absolute existential constants.']),
    'TRIPLE-SIGNED-SECTORS-001': (['signedSeries_norm_locallyUniform', 'signedSeries_locallyUniform', 'pairZeroSeries_reciprocal', 'tripleMaster_positive_kernel_identity', 'tripleMaster_positive_kernel_summable', 'tripleMaster_positive_kernel_cutoff', 'signedSector_determinant', 'signedSector_cover', 'signedSector_overlap', 'signedSector_disjoint_interiors', 'signedSector_measurePreserving', 'signedSector_seams_null', 'signedGauge_half_sum', 'signedGauge_sector', 'signedFrequency_sector', 'signedFrequency_swap', 'signedFrequency_seam_real', 'tripleMasterProduct_signed_seam_real', 'signed_coefficient_bound', 'signed_integralNorm_uniform'], [
        'Positive-base convergence, reciprocal reflection, all six sectors and seam identities, the full master identity and sharp integrated majorant are checked. The historical numerical-effectiveness qualification remains separate: inherited analytic constants are existential.']),
    'TRIPLE-SIGNED-TEST-FUNCTION-001': (['signed_compact_margin', 'signed_test_entire', 'signed_test_schwartz_inversion', 'signed_identity', 'signed_zero_sum_absolute', 'signed_frequency_integrable', 'signed_normalized_identity', 'signed_zero_identity', 'signed_independent_cutoff', 'signed_sector_decomposition', 'signedPullback_N1_bound', 'signed_limit_sector_sum', 'signed_uniform_bound', 'signed_fixed_margin_limit', 'signed_compact_limit'], [
        'The exact full-zero passage, six-sector conjugation, entire and Schwartz inversion, C1 error bound and full hexagonal-support limit are checked. The sole historical qualification remaining is numerical effectiveness: constants are existential. The horizontal kernel and complex arguments are retained; the ordinate-only error remains open.']),
    'TRIPLE-BOUNDARY-ESTIMATES-001': (['tripleBoundary_remainder_exact', 'tripleBoundary_uniform_integrated', 'tripleBoundary_origin_uniform', 'tripleBoundary_axis_uniform', 'tripleBoundary_exchanged_axis_uniform'], [
        'The integrated estimate and all three uniform local profiles, including endpoints, are checked. The historical numerical-effectiveness qualification remains separate: inherited analytic constants are existential.']),
    'TRIPLE-QUADRANT-LIMIT-001': (['tripleQuadrant_integralNorm_uniform', 'tripleQuadrant_identity', 'tripleQuadrant_zero_sum_absolute', 'tripleQuadrant_entire', 'tripleQuadrant_distribution', 'tripleQuadrant_zero_identity', 'tripleQuadrant_independent_cutoff', 'tripleQuadrantN1_bounds', 'tripleBoundary_origin_mass_closed', 'tripleBoundary_axis_mass', 'tripleQuadrant_uniform_bound', 'tripleQuadrant_fixed_margin_limit'], [
        'The full quadrant identity, entire and tempered-distribution passage, exact one-sided masses, N1 error bound and fixed-test height limit are checked. The historical numerical-effectiveness qualification remains unformalized. No signed-sector or ordinate-only conclusion follows.']),
    'TRIPLE-TEST-FUNCTION-001': (['tripleTest_compact_margin', 'complexFourier_entire', 'complexFourier_schwartz_inversion', 'tripleTest_phase', 'tripleTest_integralNorm_summable', 'tripleTest_integralNorm_uniform', 'tripleTest_identity', 'tripleTest_zero_sum_absolute', 'tripleTest_frequency_integrable', 'tripleTest_bound', 'tripleTest_interior_limit', 'tripleTest_nonempty', 'tripleTest_independent_cutoff', 'tripleTest_theorem'], [
        'The entire extension, Schwartz inversion, exact weighted full-zero identity, absolute convergence, local-spacing bound and fixed-test limit are checked. The sole historical qualification remaining is numerical effectiveness: the absolute constants are existential. The scaling proof directly sets R=(T/(2pi))^epsilon in checked lower-scale bounds.']),
    'TRIPLE-INTERIOR-VANISHING-001': (['tripleInterior_retained_lower_scale', 'tripleInterior_retained_bound', 'tripleInterior_observable_bound', 'tripleInterior_retained_limit', 'tripleInterior_observable_limit', 'tripleInterior_fixed_weight_limit', 'tripleInterior_power_endpoints', 'tripleInterior_exchange', 'tripleInterior_height_three'], [
        'Both quantitative interior bounds and the uniform moving-range limits are checked. The historical numerical-effectiveness assertion remains unformalized: the absolute constants are existential through the diagonal and prime mean-square inputs.']),
    'TRIPLE-RETAINED-001': (['tripleMixedDiagonal_asymptotic', 'tripleMixedDiagonal_asymptotic_symmetric', 'tripleMixedDiagonal_finite_error_identity', 'tripleMixedDiagonal_integer_split', 'tripleSmoothingMoment_sharp', 'tripleSmoothingMean_manuscript', 'tripleSmoothingError_integral', 'tripleProperPower_count', 'triplePrimeResonantMass_decay', 'triplePrimeResonantMass_uniform_vanishing', 'tripleRetained_evaluation', 'tripleRetained_combined_bound', 'tripleRetained_height_three'], [
        'The full mathematical retained-term evaluation, its named bounds and combined additive estimate are checked. The sole remaining qualification is the historical numerical-effectiveness assertion for the mixed-diagonal constant: the formal constant is existential. Smoothing and resonance constants are explicit.']),
    'TRIPLE-LOG-GAP-001': (['tripleLogGap_summable', 'tripleLogGap_bound'], []),
    'TRIPLE-UNIFORM-001': (
        ['tripleBudget_exact', 'tripleBudget_refinement', 'tripleBudget_refined_bound',
         'tripleBudget_word_bound', 'tripleBudgetPrime_norm_envelope', 'tripleBudgetOmega_bound',
         'tripleBudgetDiagonal_uniform', 'tripleBudgetMoment_bounds', 'tripleBudget_remainder_count',
         'tripleBudget_refinement_count', 'tripleBudget_PPA_bound', 'tripleBudget_PAA_bound',
         'tripleBudget_APA_bound', 'tripleBudget_AAP_bound', 'tripleBudget_PAPoff_coarse',
         'tripleBudget_APPoff_coarse', 'tripleBudget_PPP_coarse'],
        ['The pair mean-square and diagonal constants remain existential; the historical effective-constant qualification is not formalized.',
         'Coarse word bounds retain actual weighted L2 norms and masses, with separate checked envelope comparisons; no single packaged manuscript-bound record is asserted.']),
    'TRIPLE-OFFDIAG-001': (
        ['tripleBudget_PAPoff_rate', 'tripleBudget_APPoff_rate', 'tripleBudget_PPPoff_rate',
         'tripleArithmeticConvolution_diagonal', 'tripleLogCoefficient_energy_bound',
         'tripleLogConvolution_energy_bound', 'triplePrimeMassConstant_closed'],
        ['The mixed logarithmic factor is stated as sqrt(ell_x^3 ell_z^3); translation to the literal fractional-power typography is not a separate checked declaration.']),
    'TRIPLE-SMOOTHED-ADDITIVE-001': (
        ['tripleBudget_remainder_words_uniform', 'tripleBudget_uniform_lower_scale',
         'tripleBudget_uniform_asymptotic', 'tripleBudget_uniform_additive_limit'],
        ['The absolute constant is existential through the pair mean-square input; the historical effective-constant qualification remains unformalized.']),

    'PAIR-TRANSLATION-001': (
        ['pairComplexFourier_integrable', 'pairComplexFourier_real', 'pairComplexFourier_argument',
         'pairFourierStatistic_identity', 'pairFrequencyTerm_horizontal', 'pairFrequencyTerm_index_diagonal',
         'pairWindow_fiber_card', 'pairFrequencyTerm_equal_zero_diagonal', 'pairFrequencyTerm_reflection',
         'pairScale_positive', 'pairScale_normalization', 'pairScale_argument', 'pairScale_phase',
         'pairScale_support', 'pairScale_power', 'pairScale_correlation', 'pairScale_jacobian',
         'pairScale_integrated'], []),
    'PAIR-ASYMPTOTIC-001': (
        ['pairNormalized_decomposition', 'pairNormalized_errors', 'pairNormalized_comparison_scales',
         'pairNormalized_base_bound', 'pairNormalized_power', 'pairNormalized_nonnegative_frequency',
         'pairNormalized_asymptotic', 'pairNormalized_origin', 'pairNormalized_endpoint_scales',
         'pairNormalized_endpoints', 'pairNormalized_minimal_height'],
        ['The full normalized inequality on T>=3, |alpha|<=1 and all endpoints are checked with existential constants using the pinned PREPRINT comparison. The historical effective-constant assertion and classical KV dependency route remain separate.']),
    'PAIR-POSITIVITY-001': (
        ['pairCorrelationSum_im', 'pairCorrelationSum_re_nonneg', 'pairCorrelationSum_inv',
         'pairNormalizedCorrelation_complex', 'pairNormalizedCorrelation_nonneg',
         'pairNormalizedCorrelation_even', 'pairNormalizedCorrelation_abs'], []),
    'PAIR-NORM-INTEGRAL-001': (
        ['pairKernelProduct_integrable', 'pairKernelIntegral_eq', 'pairKernelIntegral_coincident'],
        ['The two-factor profile needed for actual zero pairs is checked on |e|,|f|<=3/4, including coincident poles. The full historical complex-parameter strip and explicit semicircle bound remain separate.']),
    'PAIR-NORM-001': (
        ['pairZeroVector_product_integral', 'pairZeroWindow_square_integrable', 'pairZeroWindow_reflection',
         'pairCorrelationSum_norm', 'pairCorrelationSum_im', 'pairCorrelationSum_re_nonneg'],
        ['The exact finite norm identity and integrability are checked for every X>0 and all real T. The explicit 512/27 tail bound remains unformalized.']),
    'PAIR-TRUNC-001': (
        ['pairZeroVector_summable', 'pairZeroFullVector_phase', 'pairZeroMeanSquare_eq_full',
         'pairZero_errors_integrable', 'pairZero_window_integral_split', 'pairZero_decomposition',
         'pairZero_decomposition_manuscript', 'pairZeroExtensionError_nonpos',
         'pairZero_decomposition_unit', 'pairZero_empty_window', 'pairZero_height_zero',
         'pairZeroHorizontalEnvelope_nonneg', 'pairZeroHorizontalEnvelope_lt', 'pairZeroHorizontalEnvelope_abs',
         'pairZeroHorizontalEnvelope_empty', 'pairZeroTruncError_bound', 'pairZeroTruncError_simple_bound',
         'pairZeroHeightError_bound', 'pairZeroExtensionError_bound', 'pairZeroUniformBounds',
         'pairZeroUniformBounds_envelope', 'pairZeroCutoff_admissible', 'pairZeroCutoff_log',
         'pairZeroCutoff_errors', 'pairZeroComparison_smallHeight', 'pairZeroComparison_optimized'],
        ['The exact decomposition is checked for X>=1,T,Z>=0; all three named uniform errors and the finite horizontal envelope are checked for X>=1,T>=3,Z>=2T with existential absolute constants. The optimized cutoff and small-height O(X) absorption are now checked. The historical effective-constant assertion remains unformalized.']),
    'PAIR-COMPARE-001': (
        ['pairZeroHorizontalEnvelope_strip', 'pairZeroComparison_log_absorption',
         'pairZeroComparison_weight_absorption', 'pairZeroComparison_strip_optimized',
         'pairZeroComparison_uniform_errors', 'pairZeroComparison_uniform'],
        ['The uniform O(T)+O(X) comparison is checked using the pinned PREPRINT QRH-STRIP-001 with existential constants. The historical Korobov-Vinogradov/low-height dependency chain and effective constants remain unformalized.']),
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
    'TRIPLE-SMOOTHED-CORRELATION-001': (['smoothedTripleTerm_frozen', 'smoothedTripleTerm_summable', 'smoothedTripleTerm_cutoff', 'smoothedTripleTerm_height_cutoff', 'smoothedTripleTerm_profile', 'smoothedTriple_norm_scale', 'smoothedTriple_separate_bound', 'smoothedTriple_errors_nonneg', 'smoothedTriple_uniform_bound', 'smoothedWeightSup_bounds', 'smoothedWeight_derivative_sup', 'smoothedTriple_sup_bound', 'smoothedTripleStatistic_profile_sum', 'smoothedTripleStatistic_limit', 'smoothedTripleStatistic_compact_limit', 'smoothedTripleStatistic_varying_error', 'smoothedTripleStatistic_cutoff', 'smoothedTripleStatistic_height_cutoff', 'smoothedTripleStatistic_zero_test', 'smoothedTriple_theorem'], ['The observable, absolute convergence, cutoffs, exact benchmark, uniform named errors and fixed/varying-family limits are checked. Numerical effectiveness of inherited constants remains uncertified.']),
    'TRIPLE-MASTER-001': (
        ['integral_occurrence_sum', 'integral_occurrence_cutoff_limit', 'actualProfile_integrable',
         'tripleMasterTerm_integrable', 'tripleMasterTerm_bound', 'tripleMaster_finite_kernel',
         'tripleMaster_finite_majorant', 'tripleMasterMajorant_integral',
         'tripleMaster_integralNorm_bound', 'tripleMaster_uniform_integralNorm',
         'tripleMaster_sum_integral', 'tripleMaster_independent_cutoff_limit',
         'tripleMaster_height_cutoff_limit', 'tripleMaster_minimal_parameters',
         'tripleMaster_product_eq', 'tripleMaster_phase_cancel', 'tripleMasterTerm_eq_kernel',
         'tripleMasterKernel_integrable', 'tripleMasterProduct_integrable',
         'tripleMasterKernel_normalization', 'tripleMaster_kernel_norm_summable',
         'tripleMaster_kernel_identity', 'tripleMasterObservable_independent_cutoff',
         'tripleMasterObservable_height_cutoff', 'tripleMaster_kernel_minimal',
         'tripleMasterPattern_allEqual', 'tripleMasterPattern_only01', 'tripleMasterPattern_only02',
         'tripleMasterPattern_only12', 'tripleMasterPattern_allDistinct',
         'tripleMasterPattern_norm_summable', 'tripleMasterPattern_integralNorm_summable',
         'tripleMasterPattern_integralNorm_le', 'tripleMasterPattern_integral_identity',
         'tripleMaster_pattern_decomposition', 'tripleMaster_rows_norm_summable',
         'tripleMaster_five_subseries', 'tripleMasterPattern_finite_integral',
         'tripleMasterPattern_independent_cutoff', 'tripleMasterPattern_height_cutoff',
         'tripleMasterPattern_integral_cutoff', 'tripleMasterPattern_integral_height_cutoff',
         'tripleMasterPattern_minimal', 'tripleMasterPattern_empty_slot',
         'tripleComponent_remainder', 'tripleComponent_explicit_formula',
         'tripleComponent_continuous', 'tripleSmoothedIntegral_normalization',
         'tripleWordIntegrand_integrable', 'tripleWord_algebra',
         'tripleMasterProduct_word_expansion', 'tripleMaster_word_expansion',
         'tripleWordTable_nodup', 'tripleWordTable_complete', 'tripleWordTable_correct',
         'tripleWord_counts', 'tripleMaster_table_expansion', 'tripleMaster_word_split',
         'tripleMaster_word_minimal',
         'triplePrimeCoefficient_nonneg',
         'triplePrimeCoefficient_summable',
         'triplePrimeCoefficient_mass',
         'triplePrimeFrequency_phase',
         'triplePrimeTerm_phase',
         'triplePrimeTerm_norm',
         'triplePrimeTerm_integrable',
         'triplePrimeTerm_integralNorm',
         'triplePrime_integralNorm',
         'triplePrime_pointwise_summable',
         'triplePrimeTerm_fourier',
         'triplePrime_finite_product',
         'triplePrime_product_eq',
         'triplePrimeFourier_summable',
         'triplePrimeFourier_norm_bound',
         'triplePrime_sum_integral',
         'triplePrime_fourier_identity',
         'triplePrime_signed_PPP',
         'triplePrimeFourier_finite_cutoff',
         'triplePrimeFourier_integer_cutoff',
         'triplePrime_finite_integral',
         'triplePrime_integral_finite_cutoff',
         'triplePrime_integral_integer_cutoff',
         'triplePrimeFrequency_resonance',
         'triplePrimeFourier_resonance',
         'triplePrimeFourier_integer_one',
         'triplePrime_fourier_minimal',
         'triplePrimeFourier_zero_weight',
         'triplePrimeFourier_neg_weight',
         'pairMeanPrimeCoefficient_ne_zero',
         'triplePrimeCoefficient_ne_zero',
         'primePower_unique',
         'primePowerIndex_values',
         'primePowerIndex_injective',
         'primePowerIndex_supported',
         'primePower_resonance_exists',
         'triplePrimeResonance_classification',
         'triplePrimeResonance_nonzero',
         'primePowerIndex_bijective',
         'primePower_resonance_unique',
         'triplePrimeResonantMass_summable',
         'triplePrimeResonantMass_norm_summable',
         'triplePrimeResonantMass_reindex',
         'triplePrimeResonantMass_nested',
         'triplePrimeResonantMass_nonneg',
         'triplePrimeResonantMass_bound',
         'triplePrime_resonant_norm_summable',
         'triplePrime_off_norm_summable',
         'triplePrime_resonant_series',
         'triplePrime_resonance_split',
         'triplePrime_resonance_signed',
         'triplePrime_resonance_unit_mass',
         'primePowerIndex_excludes_one',
         'primePowerIndex_equal_exponents',
         'primePowerIndex_ordered',
         'primePowerIndex_first',
         'primePower_distinct_product',
         'triplePrimeResonance_two_three',
         'triplePrimeOffSeries_zero_weight',
         'triplePrimeOffSeries_neg_weight',
         'triplePrime_resonance_minimal',
         'fourierDecay_derivative_support',
         'fourierDecay_derivative_compact',
         'fourierDecay_derivative_integrable',
         'pairMeanFourier_iteratedDeriv',
         'pairMeanFourier_power_bound',
         'pairMeanFourier_decay',
         'fourierDecay_iteratedDeriv_ofReal',
         'fourierDecay_ofReal_compact',
         'fourierDerivativeL1_nonneg',
         'fourierDerivativeL1_zero_order',
         'fourierDecay_real_power_bound',
         'fourierDecay_real_bound',
         'fourierDecay_real_mass',
         'fourierDecay_real_min',
         'fourierDecay_real_uniform',
         'fourierDecay_zero_frequency',
         'fourierDecay_first_order',
         'fourierDerivativeL1_zero_weight',
         'fourierDerivativeL1_neg_weight',
         'fourierDecay_real_neg_weight',
         'fourierDecay_order_zero',
         'fourierDecay_unit_frequencies',
         'triplePrimeFrequency_eq_zero',
         'triplePrimeFrequency_ne_zero',
         'triplePrimeFrequency_decay_scale',
         'tripleWeight_fourier_decay',
         'tripleWeight_fourier_smooth',
         'tripleWeight_cubic_decay',
         'triplePrimeFourierTerm_norm_factor',
         'triplePrimeFourierTerm_mass_bound',
         'triplePrimeFourierTerm_decay',
         'tripleWeight_cubic_uniform',
         'triplePrimeFourierTerm_decay_minimal',
         'tripleMasterProduct_swap',
         'tripleMasterObservable_swap',
         'tripleMasterObservable_integral_series',
         'tripleMasterObservable_norm_bound',
         'tripleMaster_assembled',
         'tripleMaster_uniform',
         'tripleMaster_weight_mass_one',
         'tripleMaster_manuscript',
         'tripleMasterObservable_neg',
         'tripleMasterL1Bound_neg',
         'tripleMaster_assembled_minimal',
         'tripleMaster_assembled_zero',
         'tripleMaster_assembled_neg',
         'tripleMaster_assembled_swapped'],
        ['The assembled master statement, symmetry, observable norm and manuscript specialization are checked with one universal existential constant; only the historical numerical-effectiveness qualification of the counting constant remains unformalized.']),
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
    'ORDINATE-CONSTANT-KERNEL-001': (['evaluated_integrals_summable', 'evaluated_integrals_cutoff_limit', 'complexFourier_eq_inverse', 'actual_anchored_tail', 'actual_signed_eight_reflections', 'actualProfile_symmetric_second', 'actualProfile_symmetric_fourth', 'actual_horizontal_uniform_bounds', 'anchored_decay_twentieth_tail', 'constantKernelEmpty_profile', 'constantKernelEmpty_symmetric', 'constantKernelEmpty_horizontal_bound', 'constantKernelEmpty_global_bound', 'constantKernel_real_gap_bound', 'constantKernelEmpty_pointwise', 'constantKernelEmpty_origin', 'constantKernelEmpty_coincident', 'constantKernelEmpty_cube_endpoints', 'replacementRadius_nonneg', 'replacementHorizontal_bounds', 'constantKernelEmpty_scaled', 'replacementKernel_scaled', 'replacementPartial_smooth', 'replacementDeriv_succ', 'replacementDeriv_succ_right', 'replacementDeriv_smooth', 'replacementDeriv_support', 'replacementDeriv_compact', 'replacementDeriv_integrable', 'replacementDeriv_add', 'replacementDeriv_product_bound', 'replacementP24_nonneg', 'replacementP24_pure', 'replacementExpRemainder_smooth', 'replacementPartial_exp', 'replacementExpRemainder_first', 'replacementExpRemainder_higher', 'replacementExpRemainder_jet_bound', 'replacementFourier_partial', 'replacementFourier_power', 'replacementFourier_L1', 'replacementFourier_decay', 'replacementLinear_apply', 'replacementLinear_bounds', 'replacementLinear_sum_zero', 'replacementCosh_remainders', 'replacementAmplitude_L1', 'replacementRemainder_fourier_bound', 'replacementCosh_smooth', 'replacementCosh_fourier_sum', 'replacementCosh_fourier_bound', 'replacementHeight_bounds', 'replacementTuple_bound', 'replacement_anchor_decay_summable', 'replacementWeight_bounds', 'replacementWeight_zero', 'replacementMomentTerm_nonneg', 'replacementMoment_summable', 'replacementTuple_weighted_summable', 'replacementKernel_global', 'replacement_errors_summable', 'replacement_error_split', 'replacement_absorb_decay', 'replacement_large_height', 'replacementTerm_bound', 'replacementError_bound', 'replacementError_cutoff', 'replacementTuple_zero_test', 'replacementTuple_zero_displacement', 'replacementError_zero_test', 'replacementMoment_nonneg', 'replacementKernel_equal_ordinates', 'replacementKernel_height_endpoint', 'replacementTuple_height_endpoint', 'replacementError_normalization', 'replacementConstantError_cutoff', 'replacementEvenError_cutoff'], ['The pointwise and project-scaled estimates, exact P24 quadratic Fourier decay, fixed-height absolute convergence, independent cutoffs, normalized summed moment bound and algebraic even-error split are checked. Density-based replacement vanishing and identification of the constant term with the unaveraged signed full-zero statistic remain unformalized. The kernel-free signed complex-argument error remains open.', 'No interchange of the kernel-free infinite zero sum with the unevaluated Fourier integral is supplied.']),
    'PAIR-COUNT-001': (
        ['zeroMultiplicity_pos', 'occurrenceCutoff_card', 'occurrence_count_local', 'occurrence_count_interval', 'occurrence_count_logarithmic',
         'zeta23_dyadic_occurrences', 'zeta23_dyadic_closed_occurrences'],
        ['The local logarithmic and inclusive cumulative upper counts are checked with existential constants.',
         'Dyadic Riemann-von Mangoldt with its main term and arbitrary endpoints is checked. Sharp cumulative Riemann-von Mangoldt, exclusion of real strip zeros and numerical effectiveness remain separate.']),
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
    zeta23 = json.loads(read('research/lean-zeta23-inventory.json'))
    found = []
    for module in zeta23['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished Zeta23 adapter: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in zeta23['components']],
            'Zeta23 inventory differs from source declarations')
    checked = []
    for suite in ['zeta23-ranktrace', 'zeta23-counting']:
        cfg = json.loads(read('lean/VerificationChallenges/' + suite + '.json'))
        require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
                'changed Zeta23 verification scope')
        checked.extend(cfg['theorem_names'])
    require(checked == [c['declaration'] for c in zeta23['components'] if c['comparator_checked']],
            'Zeta23 Comparator coverage differs from inventory')
    components.extend(zeta23['components'])
    names.extend(c['declaration'] for c in zeta23['components'])
    pair_zero = json.loads(read('research/lean-pair-zero-inventory.json'))
    found = []
    for module in pair_zero['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair zero-side solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in pair_zero['components']],
            'pair zero-side inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/pair-zero.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in pair_zero['components'] if c['comparator_checked']],
            'pair zero-side Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed pair zero-side verification scope')
    components.extend(pair_zero['components'])
    names.extend(c['declaration'] for c in pair_zero['components'])
    pair_zero_bounds = json.loads(read('research/lean-pair-zero-bounds-inventory.json'))
    found = []
    for module in pair_zero_bounds['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair zero-side bounds solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in pair_zero_bounds['components']],
            'pair zero-side bounds inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/pair-zero-bounds.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in pair_zero_bounds['components'] if c['comparator_checked']],
            'pair zero-side bounds Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed pair zero-side bounds verification scope')
    components.extend(pair_zero_bounds['components'])
    names.extend(c['declaration'] for c in pair_zero_bounds['components'])
    pair_zero_comparison = json.loads(read('research/lean-pair-zero-comparison-inventory.json'))
    found = []
    for module in pair_zero_comparison['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair zero-side comparison solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in pair_zero_comparison['components']],
            'pair zero-side comparison inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/pair-zero-comparison.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in pair_zero_comparison['components'] if c['comparator_checked']],
            'pair zero-side comparison Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed pair zero-side comparison verification scope')
    components.extend(pair_zero_comparison['components'])
    names.extend(c['declaration'] for c in pair_zero_comparison['components'])
    pair_asymptotic = json.loads(read('research/lean-pair-asymptotic-inventory.json'))
    found = []
    for module in pair_asymptotic['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished normalized pair asymptotic solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in pair_asymptotic['components']],
            'normalized pair asymptotic inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/pair-asymptotic.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in pair_asymptotic['components'] if c['comparator_checked']],
            'normalized pair asymptotic Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed normalized pair asymptotic verification scope')
    components.extend(pair_asymptotic['components'])
    names.extend(c['declaration'] for c in pair_asymptotic['components'])
    pair_fourier = json.loads(read('research/lean-pair-fourier-inventory.json'))
    found = []
    for module in pair_fourier['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished pair Fourier passage solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in pair_fourier['components']],
            'pair Fourier passage inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/pair-fourier.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in pair_fourier['components'] if c['comparator_checked']],
            'pair Fourier passage Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed pair Fourier passage verification scope')
    components.extend(pair_fourier['components'])
    names.extend(c['declaration'] for c in pair_fourier['components'])
    triple_master = json.loads(read('research/lean-triple-master-inventory.json'))
    found = []
    for module in triple_master['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished triple master integral-norm bound solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_master['components']],
            'triple master integral-norm bound inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-master.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_master['components'] if c['comparator_checked']],
            'triple master integral-norm bound Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed triple master integral-norm bound verification scope')
    components.extend(triple_master['components'])
    names.extend(c['declaration'] for c in triple_master['components'])
    triple_budget = json.loads(read('research/lean-triple-budget-inventory.json'))
    found = []
    for module in triple_budget['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished uniform triple error budget solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_budget['components']],
            'uniform triple error budget inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-budget.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_budget['components'] if c['comparator_checked']],
            'uniform triple error budget Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed uniform triple error budget verification scope')
    components.extend(triple_budget['components'])
    names.extend(c['declaration'] for c in triple_budget['components'])
    triple_mixed_diagonal = json.loads(read('research/lean-triple-mixed-diagonal-inventory.json'))
    found = []
    for module in triple_mixed_diagonal['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished uniform mixed-prime diagonal solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_mixed_diagonal['components']],
            'uniform mixed-prime diagonal inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-mixed-diagonal.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_mixed_diagonal['components'] if c['comparator_checked']],
            'uniform mixed-prime diagonal Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed uniform mixed-prime diagonal verification scope')
    components.extend(triple_mixed_diagonal['components'])
    names.extend(c['declaration'] for c in triple_mixed_diagonal['components'])
    triple_smoothing = json.loads(read('research/lean-triple-smoothing-inventory.json'))
    found = []
    for module in triple_smoothing['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished sharp first smoothing moment solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_smoothing['components']],
            'sharp first smoothing moment inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-smoothing.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_smoothing['components'] if c['comparator_checked']],
            'sharp first smoothing moment Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed sharp first smoothing moment verification scope')
    components.extend(triple_smoothing['components'])
    names.extend(c['declaration'] for c in triple_smoothing['components'])
    triple_resonance_decay = json.loads(read('research/lean-triple-resonance-decay-inventory.json'))
    found = []
    for module in triple_resonance_decay['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished decaying resonance bound solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_resonance_decay['components']],
            'decaying resonance bound inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-resonance-decay.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_resonance_decay['components'] if c['comparator_checked']],
            'decaying resonance bound Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed decaying resonance bound verification scope')
    components.extend(triple_resonance_decay['components'])
    names.extend(c['declaration'] for c in triple_resonance_decay['components'])
    triple_retained = json.loads(read('research/lean-triple-retained-inventory.json'))
    found = []
    for module in triple_retained['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished retained-term evaluation solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_retained['components']],
            'retained-term evaluation inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-retained.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_retained['components'] if c['comparator_checked']],
            'retained-term evaluation Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed retained-term evaluation verification scope')
    components.extend(triple_retained['components'])
    names.extend(c['declaration'] for c in triple_retained['components'])
    triple_interior_vanishing = json.loads(read('research/lean-triple-interior-vanishing-inventory.json'))
    found = []
    for module in triple_interior_vanishing['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished interior-vanishing corollary solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_interior_vanishing['components']],
            'interior-vanishing corollary inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-interior-vanishing.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_interior_vanishing['components'] if c['comparator_checked']],
            'interior-vanishing corollary Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed interior-vanishing corollary verification scope')
    components.extend(triple_interior_vanishing['components'])
    names.extend(c['declaration'] for c in triple_interior_vanishing['components'])
    triple_test_function = json.loads(read('research/lean-triple-test-function-inventory.json'))
    found = []
    for module in triple_test_function['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished interior weighted test-function passage solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_test_function['components']],
            'interior weighted test-function passage inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-test-function.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_test_function['components'] if c['comparator_checked']],
            'interior weighted test-function passage Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed interior weighted test-function passage verification scope')
    components.extend(triple_test_function['components'])
    names.extend(c['declaration'] for c in triple_test_function['components'])
    triple_boundary = json.loads(read('research/lean-triple-boundary-inventory.json'))
    found = []
    for module in triple_boundary['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished quadrant boundary passage solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_boundary['components']],
            'quadrant boundary passage inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-boundary.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_boundary['components'] if c['comparator_checked']],
            'quadrant boundary passage Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed quadrant boundary passage verification scope')
    components.extend(triple_boundary['components'])
    names.extend(c['declaration'] for c in triple_boundary['components'])
    triple_signed = json.loads(read('research/lean-triple-signed-sectors-inventory.json'))
    found = []
    for module in triple_signed['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished signed-sector passage solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_signed['components']],
            'signed-sector passage inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-signed-sectors.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_signed['components'] if c['comparator_checked']],
            'signed-sector passage Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed signed-sector passage verification scope')
    components.extend(triple_signed['components'])
    names.extend(c['declaration'] for c in triple_signed['components'])
    triple_localization = json.loads(read('research/lean-triple-kernel-localization-inventory.json'))
    found = []
    for module in triple_localization['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = read(path)
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M),
                'unfinished exact kernel-localization passage solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    require(found == [{k: c[k] for k in ('declaration', 'source')} for c in triple_localization['components']],
            'exact kernel-localization passage inventory differs from source declarations')
    cfg = json.loads(read('lean/VerificationChallenges/triple-kernel-localization.json'))
    require(cfg['theorem_names'] == [c['declaration'] for c in triple_localization['components'] if c['comparator_checked']],
            'exact kernel-localization passage Comparator coverage differs from inventory')
    require(cfg['permitted_axioms'] == config['permitted_axioms'] and cfg['enable_nanoda'] is False,
            'changed exact kernel-localization passage verification scope')
    components.extend(triple_localization['components'])
    names.extend(c['declaration'] for c in triple_localization['components'])
    from check_lean_triple_sine_measure import validate as validate_sine
    triple_sine = json.loads(read('research/lean-triple-sine-measure-inventory.json'))
    validate_sine(triple_sine, json.loads(read('lean/VerificationChallenges/triple-sine-measure.json')))
    components.extend(triple_sine['components'])
    names.extend(c['declaration'] for c in triple_sine['components'])
    from check_lean_triple_main_term_comparison import validate as validate_comparison
    triple_comparison = json.loads(read('research/lean-triple-main-term-comparison-inventory.json'))
    validate_comparison(triple_comparison, json.loads(read('lean/VerificationChallenges/triple-main-term-comparison.json')))
    components.extend(triple_comparison['components'])
    names.extend(c['declaration'] for c in triple_comparison['components'])
    from check_lean_triple_smoothed_correlation import validate as validate_smoothed
    triple_smoothed = json.loads(read('research/lean-triple-smoothed-correlation-inventory.json'))
    validate_smoothed(triple_smoothed, json.loads(read('lean/VerificationChallenges/triple-smoothed-correlation.json')))
    components.extend(triple_smoothed['components'])
    names.extend(c['declaration'] for c in triple_smoothed['components'])
    from check_lean_constant_kernel import validate as validate_constant
    constant = json.loads(read('research/lean-constant-kernel-inventory.json'))
    validate_constant(constant, json.loads(read('lean/VerificationChallenges/constant-kernel.json')))
    components.extend(constant['components'])
    names.extend(c['declaration'] for c in constant['components'])
    from check_lean_density_adapters import validate as validate_density
    density = json.loads(read('research/lean-density-adapters-inventory.json'))
    validate_density(density, json.loads(read('lean/VerificationChallenges/density-adapters.json')))
    components.extend(density['components'])
    names.extend(c['declaration'] for c in density['components'])
    from check_lean_littlewood import validate as validate_littlewood
    littlewood = json.loads(read('research/lean-littlewood-inventory.json'))
    validate_littlewood(littlewood, json.loads(read('lean/VerificationChallenges/littlewood.json')))
    components.extend(littlewood['components'])
    names.extend(c['declaration'] for c in littlewood['components'])
    require(len(names) == len(set(names)), 'duplicate cross-milestone declaration')
    axioms = re.findall(r'^#print axioms (\S+)$', read('lean/HigherCorrelations/AxiomReport.lean'), re.M)
    require(set(names + actual['imported_axioms'] + profile['imported_axioms'] + uniform['imported_axioms'] + pair['imported_axioms'] + mellin['imported_axioms'] + exact['imported_axioms'] + pair_uniform['imported_axioms'] + meanvalue['imported_axioms'] + sieve['imported_axioms'] + diagonal['imported_axioms'] + prime_mean['imported_axioms'] + rhs_mean['imported_axioms'] + zeta23['imported_axioms'] + pair_zero['imported_axioms'] + pair_zero_bounds['imported_axioms'] + pair_zero_comparison['imported_axioms'] + pair_asymptotic['imported_axioms'] + pair_fourier['imported_axioms'] + triple_master['imported_axioms'] + triple_budget['imported_axioms'] + triple_mixed_diagonal['imported_axioms'] + triple_smoothing['imported_axioms'] + triple_resonance_decay['imported_axioms'] + triple_retained['imported_axioms'] + triple_interior_vanishing['imported_axioms'] + triple_test_function['imported_axioms'] + triple_boundary['imported_axioms'] + triple_signed['imported_axioms'] + triple_localization['imported_axioms']) <= set(axioms) and len(axioms) == len(set(axioms)), 'axiom report coverage')
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
        next_step='The exact, tuplewise and summed near/far localization estimates and complex-test weighted frozen-profile summability are checked. Normalized correlation transfer and its fixed-test height limit are checked. The effective uniform microscopic profile limit is also checked. The critical-line quadratic expansion and tuplewise specialization are checked. The explicit zero-gap horizontal formula and closed-cube positivity are checked. The local normalization identity and coefficient limit 3/2 are checked, completing formal coverage of TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001. The complete five-partition sine benchmark, tempered Fourier identity and ordinary/factorial cumulants are checked, including closed-hexagon cancellation. The exact main-term comparison, weighted estimates and fixed-test limits are checked with inherited existential constants. The unit-normalized smoothed triple theorem is assembled, including absolute convergence, cutoffs, uniform errors and varying-family limits. Its inherited effectivity qualification remains outstanding. Pointwise constant-kernel replacement, its project-scaled bound, quadratic P24 Fourier decay, absolute convergence, cutoffs, exact algebraic split and summed moment bound are checked with explicit conservative constants. Finite density-count and reflection/window adapters and Littlewood rectangle counting on zero-free boundaries are checked. Discharge the explicit UniformDyadicDensity hypothesis and separately prove the needed close-pair bound before density-based moment or vanishing claims. The unaveraged constant-term identification remains separate. Numerical effectiveness of inherited smoothed-theorem constants and the ordinate-only signed error remain separate.')


def validate(record):
    require(record == derive(), 'stale or overstated analytic formalization coverage')


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.record = json.loads(RECORD.read_text())

    def test_littlewood_preserves_density_boundary(self):
        node = next(n for n in derive()['nodes'] if n['id'] == 'ORDINATE-DENSITY-INPUT-001')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.littlewood_identity', node['components'])
        self.assertIn('HigherCorrelations.littlewood_zeta_budget_positive_height', node['components'])
        self.assertIn('zero-free boundaries', node['remaining_obligations'][0])

    def test_density_input_remains_conditional(self):
        node = next(n for n in derive()['nodes'] if n['id'] == 'ORDINATE-DENSITY-INPUT-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertEqual(node['ledger_status'], 'proved-draft')
        self.assertIn('HigherCorrelations.density_scaled_tail_bound', node['components'])
        self.assertIn('explicit UniformDyadicDensity hypothesis', node['remaining_obligations'][0])

    def test_constant_kernel_partial_boundary(self):
        node = next(n for n in derive()['nodes'] if n['id'] == 'ORDINATE-CONSTANT-KERNEL-001')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.constantKernelEmpty_pointwise', node['components'])
        self.assertIn('Density-based replacement vanishing', node['remaining_obligations'][0])
        self.assertIn('HigherCorrelations.replacementError_bound', node['components'])
        self.assertIn('HigherCorrelations.replacementTuple_bound', node['components'])

    def test_smoothed_theorem_preserves_effectivity_boundary(self):
        node = next(n for n in derive()['nodes'] if n['id'] == 'TRIPLE-SMOOTHED-CORRELATION-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertEqual(node['ledger_status'], 'proved-draft')
        for name in ['smoothedTriple_theorem', 'smoothedTripleStatistic_profile_sum',
                     'smoothedTripleTerm_summable', 'smoothedTripleStatistic_height_cutoff',
                     'smoothedTriple_sup_bound', 'smoothedTripleStatistic_varying_error']:
            self.assertIn('HigherCorrelations.' + name, node['components'])
        self.assertTrue(any('effectiveness' in gap for gap in node['remaining_obligations']))

    def test_main_term_comparison_preserves_effectivity_boundary(self):
        nodes = {n['id']: n for n in derive()['nodes']}
        node = nodes['TRIPLE-MAIN-TERM-COMPARISON-001']
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertEqual(node['ledger_status'], 'proved-draft')
        for name in ['mainTermPhysicalTest_apply', 'sineBenchmark_reflection',
                     'sineBenchmarkSpectrum_closed', 'mainTermComparison_exact',
                     'mainTerm_signed_bound', 'mainTerm_frozen_bound_deriv',
                     'mainTerm_signed_normalized_limit', 'mainTerm_frozen_normalized_limit']:
            self.assertIn('HigherCorrelations.' + name, node['components'])
        self.assertTrue(any('effectiveness' in gap for gap in node['remaining_obligations']))
        self.assertFalse(nodes['ORDINATE-TRIPLE-001']['whole_claim_formalized'])

    def test_sine_benchmark_complete_without_global_promotion(self):
        nodes = {n['id']: n for n in derive()['nodes']}
        node = nodes['TRIPLE-SINE-MEASURE-001']
        self.assertEqual(node['coverage'], 'formalized')
        self.assertTrue(node['whole_claim_formalized'])
        self.assertEqual(node['ledger_status'], 'proved-draft')
        self.assertIn('HigherCorrelations.sineOverlap_integral', node['components'])
        self.assertIn('HigherCorrelations.sineCycle_pairing', node['components'])
        self.assertIn('HigherCorrelations.sineSquared_pairing', node['components'])
        self.assertIn('HigherCorrelations.sineBenchmark_tempered', node['components'])
        self.assertIn('HigherCorrelations.sineBenchmark_fourier', node['components'])
        self.assertIn('HigherCorrelations.sineOrdinaryCumulant_fourier', node['components'])
        self.assertIn('HigherCorrelations.sineR3_factorial_identity', node['components'])
        self.assertIn('HigherCorrelations.sineCumulantDensity_closed', node['components'])
        self.assertEqual(node['remaining_obligations'], [])
        self.assertFalse(nodes['TRIPLE-MAIN-TERM-COMPARISON-001']['whole_claim_formalized'])

    def test_critical_specialization_complete_without_global_promotion(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001')
        self.assertEqual(node['coverage'], 'formalized')
        self.assertTrue(node['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.rationalProfile_gap_bound', node['components'])
        self.assertIn('HigherCorrelations.rationalProfile_microscopic_bound', node['components'])
        self.assertIn('HigherCorrelations.rationalProfile_microscopic_tendstoUniformlyOn', node['components'])
        self.assertIn('HigherCorrelations.rationalProfile_critical_microscopic_bound', node['components'])
        self.assertIn('HigherCorrelations.tripleMasterKernel_critical_quadratic_bound', node['components'])
        self.assertIn('HigherCorrelations.tripleMasterKernel_critical_leading_bound', node['components'])
        self.assertIn('HigherCorrelations.rationalProfile_zero_gap_horizontal', node['components'])
        self.assertIn('HigherCorrelations.zeroGapHorizontalDenominator_bounds', node['components'])
        self.assertIn('HigherCorrelations.rationalProfile_zero_gap_tendstoUniformlyOn', node['components'])
        self.assertIn('HigherCorrelations.criticalLocalNormalization_identity', node['components'])
        self.assertIn('HigherCorrelations.criticalLocalCoefficient_tendsto', node['components'])
        self.assertIn('HigherCorrelations.criticalLocalNormalization_endpoint_excluded', node['components'])
        self.assertEqual(node['remaining_obligations'], [])
        self.assertEqual(node['ledger_status'], 'proved-draft')
        self.assertFalse(self.record['whole_graph_formalized'])
        for key in ['TRIPLE-MAIN-TERM-COMPARISON-001', 'ORDINATE-TRIPLE-001']:
            other = next(n for n in self.record['nodes'] if n['id'] == key)
            self.assertFalse(other['whole_claim_formalized'])

    def test_localization_transfer_preserves_effectivity_boundary(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'TRIPLE-KERNEL-LOCALIZATION-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.tripleMasterKernel_localization', node['components'])
        self.assertIn('HigherCorrelations.tripleKernelLocalizationError_bound', node['components'])
        self.assertIn('HigherCorrelations.tripleTestKernel_localization_bound', node['components'])
        self.assertIn('HigherCorrelations.tripleKernelLocalizationError_absolutely_integrable', node['components'])
        self.assertIn('HigherCorrelations.tripleKernelLocalizationError_summed_bound', node['components'])
        self.assertIn('HigherCorrelations.tripleFrozenProfile_summable_bound', node['components'])
        self.assertIn('HigherCorrelations.tripleFrozenProfile_independent_cutoff', node['components'])
        self.assertIn('HigherCorrelations.tripleFrozenTestProfile_weighted_bound', node['components'])
        self.assertIn('HigherCorrelations.frozenStatistic_transfer_bound', node['components'])
        self.assertIn('HigherCorrelations.frozenStatistic_uniform_bound', node['components'])
        self.assertIn('HigherCorrelations.frozenStatistic_compact_limit', node['components'])
        self.assertTrue(any('Numerical effectiveness' in gap for gap in node['remaining_obligations']))
        self.assertFalse(any('remain unformalized' in gap for gap in node['remaining_obligations']))

    def test_signed_passage_preserves_effectivity_and_horizontal_boundary(self):
        for key in ['TRIPLE-SIGNED-SECTORS-001', 'TRIPLE-SIGNED-TEST-FUNCTION-001']:
            node = next(n for n in self.record['nodes'] if n['id'] == key)
            self.assertEqual(node['coverage'], 'partial')
            self.assertFalse(node['whole_claim_formalized'])
            self.assertEqual(len(node['remaining_obligations']), 1)
            self.assertIn('existential', node['remaining_obligations'][0])
        node = next(n for n in self.record['nodes'] if n['id'] == 'TRIPLE-SIGNED-TEST-FUNCTION-001')
        self.assertIn('HigherCorrelations.signed_compact_limit', node['components'])
        self.assertIn('HigherCorrelations.signed_zero_identity', node['components'])
        self.assertIn('ordinate-only error remains open', node['remaining_obligations'][0])

    def test_zero_comparison_preserves_historical_effectivity_boundary(self):
        for key in ['PAIR-NORM-INTEGRAL-001', 'PAIR-NORM-001', 'PAIR-TRUNC-001']:
            node = next(n for n in self.record['nodes'] if n['id'] == key)
            self.assertEqual(node['coverage'], 'partial')
            self.assertFalse(node['whole_claim_formalized'])
            self.assertTrue(node['remaining_obligations'])
        trunc = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-TRUNC-001')
        self.assertIn('HigherCorrelations.pairZero_decomposition', trunc['components'])
        self.assertIn('HigherCorrelations.pairZeroExtensionError_nonpos', trunc['components'])
        self.assertIn('HigherCorrelations.pairZeroUniformBounds', trunc['components'])
        self.assertIn('HigherCorrelations.pairZeroUniformBounds_envelope', trunc['components'])
        self.assertIn('HigherCorrelations.pairZeroComparison_optimized', trunc['components'])
        self.assertTrue(any('effective-constant' in gap for gap in trunc['remaining_obligations']))
        comparison = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-COMPARE-001')
        self.assertEqual(comparison['coverage'], 'partial')
        self.assertFalse(comparison['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.pairZeroComparison_uniform', comparison['components'])
        self.assertTrue(any('PREPRINT' in gap and 'Korobov-Vinogradov' in gap
                            for gap in comparison['remaining_obligations']))

    def test_triple_master_interchange_bound_partial(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'TRIPLE-MASTER-001')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertEqual(node['coverage'], 'partial')
        for name in ['tripleMaster_uniform_integralNorm', 'tripleMaster_sum_integral',
                     'tripleMaster_independent_cutoff_limit', 'tripleMaster_height_cutoff_limit',
                     'tripleMaster_product_eq', 'tripleMaster_phase_cancel',
                     'tripleMaster_kernel_identity', 'tripleMaster_kernel_norm_summable',
                     'tripleMasterKernel_normalization', 'tripleMaster_kernel_minimal',
                     'tripleMaster_five_subseries', 'tripleMaster_rows_norm_summable',
                     'tripleMasterPattern_integral_identity', 'tripleMasterPattern_integralNorm_le',
                     'tripleMasterPattern_integral_height_cutoff', 'tripleMasterPattern_minimal',
                     'tripleMaster_word_expansion', 'tripleMaster_table_expansion',
                     'tripleWordIntegrand_integrable', 'tripleWordTable_correct',
                     'tripleWord_counts', 'tripleMaster_word_split', 'tripleMaster_word_minimal',
                     'triplePrime_fourier_identity', 'triplePrimeFourier_summable',
                     'triplePrime_integralNorm', 'triplePrime_signed_PPP',
                     'triplePrimeFourier_integer_cutoff', 'triplePrimeFourier_resonance',
                     'primePower_resonance_unique', 'primePowerIndex_bijective',
                     'triplePrimeResonantMass_nested', 'triplePrimeResonantMass_reindex',
                     'triplePrime_resonance_split', 'triplePrime_resonance_signed',
                     'pairMeanFourier_iteratedDeriv', 'fourierDecay_real_bound',
                     'fourierDecay_real_power_bound', 'fourierDecay_real_min',
                     'triplePrimeFrequency_decay_scale', 'triplePrimeFourierTerm_decay',
                     'tripleMaster_assembled', 'tripleMaster_uniform',
                     'tripleMasterObservable_swap', 'tripleMasterObservable_norm_bound',
                     'tripleMaster_manuscript', 'tripleMaster_assembled_minimal']:
            self.assertIn('HigherCorrelations.' + name, node['components'])
        self.assertFalse(any('five index-pattern subseries' in gap for gap in node['remaining_obligations']))
        self.assertEqual(len(node['remaining_obligations']), 1)
        self.assertIn('numerical-effectiveness', node['remaining_obligations'][0])
        self.assertFalse(any('Fourier-decay' in gap for gap in node['remaining_obligations']))
        self.assertFalse(any('Fourier-series interchange' in gap for gap in node['remaining_obligations']))
        self.assertFalse(any('resonance classification' in gap for gap in node['remaining_obligations']))

    def test_pair_translation_complete(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-TRANSLATION-001')
        self.assertTrue(node['whole_claim_formalized'])
        self.assertEqual(node['remaining_obligations'], [])
        for name in ['pairComplexFourier_argument', 'pairFourierStatistic_identity',
                     'pairFrequencyTerm_equal_zero_diagonal', 'pairScale_integrated']:
            self.assertIn('HigherCorrelations.' + name, node['components'])

    def test_normalized_asymptotic_effectivity_and_positivity(self):
        node = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-ASYMPTOTIC-001')
        self.assertEqual(node['coverage'], 'partial')
        self.assertFalse(node['whole_claim_formalized'])
        self.assertIn('HigherCorrelations.pairNormalized_asymptotic', node['components'])
        self.assertIn('HigherCorrelations.pairNormalized_origin', node['components'])
        self.assertIn('HigherCorrelations.pairNormalized_endpoints', node['components'])
        self.assertTrue(any('effective-constant' in gap and 'PREPRINT' in gap
                            for gap in node['remaining_obligations']))
        positive = next(n for n in self.record['nodes'] if n['id'] == 'PAIR-POSITIVITY-001')
        self.assertTrue(positive['whole_claim_formalized'])
        self.assertEqual(positive['remaining_obligations'], [])

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
