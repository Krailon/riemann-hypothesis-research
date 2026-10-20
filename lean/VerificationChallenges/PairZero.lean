import HigherCorrelations.PairZeroDefinitions

/-! Independent statement surface; intentional holes belong only to the challenge. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

theorem pairKernelPole_upper (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4) (i : Fin 2) :
    0 < (pairKernelPole z (i,true)).im := by sorry

theorem pairKernelPole_lower (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4) (i : Fin 2) :
    (pairKernelPole z (i,false)).im < 0 := by sorry

theorem pairKernelPole_injective (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) : Function.Injective (pairKernelPole z) := by sorry

theorem pairKernelPole_product (z : Fin 2 → ℂ) (v : ℂ) :
    (∏ i : Fin 2 × Bool, (v-pairKernelPole z i)) =
      (1+(v-z 0)^2)*(1+(v-z 1)^2) := by sorry

theorem pairKernelPole_coefficient_upper (z : Fin 2 → ℂ) (i : Fin 2) :
    poleCoefficient (pairKernelPole z) (i,true) =
      (2*Complex.I * ∏ j ∈ Finset.univ.erase i, ((z i-z j)*(z i-z j+2*Complex.I)))⁻¹ := by sorry

theorem pairKernelPole_coefficient_lower (z : Fin 2 → ℂ) (i : Fin 2) :
    poleCoefficient (pairKernelPole z) (i,false) =
      (-2*Complex.I * ∏ j ∈ Finset.univ.erase i, ((z i-z j)*(z i-z j-2*Complex.I)))⁻¹ := by sorry

theorem pairKernel_upper_sum (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (Real.pi : ℂ) * (∑ i, (∏ j ∈ Finset.univ.erase i,
      ((z i-z j)*(z i-z j+2*Complex.I)))⁻¹) = 2*Real.pi/(4+(z 0-z 1)^2) := by sorry

theorem pairKernel_lower_sum (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (Real.pi : ℂ) * (∑ i, (∏ j ∈ Finset.univ.erase i,
      ((z i-z j)*(z i-z j-2*Complex.I)))⁻¹) = 2*Real.pi/(4+(z 0-z 1)^2) := by sorry

theorem pairKernel_pole_sum (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (∑ i : Fin 2 × Bool, poleCoefficient (pairKernelPole z) i *
      (if 0 < (pairKernelPole z i).im then Complex.I*Real.pi else -Complex.I*Real.pi)) =
      2*Real.pi/(4+(z 0-z 1)^2) := by sorry

theorem pairKernelProduct_bound (a e f t : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) :
    ‖pairKernelProduct a e f t‖ ≤ 16 / (1+t^2) := by sorry

theorem pairKernelProduct_integrable (a e f : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) :
    Integrable (pairKernelProduct a e f) := by sorry

theorem pairKernelCenters_bound (a e f : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) :
    ∀ i, |(pairKernelCenters a e f i).im| ≤ 3/4 := by sorry

theorem pairKernelIntegral_distinct (a e f : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4)
    (ha : a ≠ 0) : pairKernelIntegral a e f = pairKernelValue a e f := by sorry

theorem pairKernelIntegral_eq (a e f : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) :
    pairKernelIntegral a e f = pairKernelValue a e f := by sorry

theorem pairKernelIntegral_coincident (e : ℝ) (he : |e| ≤ 3/4) :
    pairKernelIntegral 0 e e = (Real.pi : ℂ)/2 := by sorry

theorem pairZeroVector_phase (i : ZeroOccurrence) (X t : ℝ) :
    pairZeroTerm i (X,t) = 2*Complex.exp (-Complex.I*t*Real.log X)*pairZeroVector i X t := by sorry

theorem pairZero_phase_norm (X t : ℝ) : ‖Complex.exp (-Complex.I*t*Real.log X)‖ = 1 := by sorry

theorem pairZeroVector_summable (X t : ℝ) (hX : 1 ≤ X) :
    Summable (fun i => ‖pairZeroVector i X t‖) := by sorry

theorem pairZeroFullVector_phase (X t : ℝ) (hX : 1 ≤ X) :
    pairZeroSeries (X,t) = 2*Complex.exp (-Complex.I*t*Real.log X)*pairZeroFullVector X t := by sorry

theorem pairZeroFullVector_eq (X t : ℝ) (hX : 1 ≤ X) :
    pairZeroFullVector X t = (2*Complex.exp (-Complex.I*t*Real.log X))⁻¹*pairZeroSeries (X,t) := by sorry

theorem pairZeroVector_continuous (i : ZeroOccurrence) (X : ℝ) :
    Continuous (pairZeroVector i X) := by sorry

theorem pairZeroFullVector_continuous (X : ℝ) (hX : 1 ≤ X) :
    Continuous (pairZeroFullVector X) := by sorry

theorem pairZeroCutoffVector_continuous (X Z : ℝ) :
    Continuous (pairZeroCutoffVector X Z) := by sorry

theorem pairZeroWindowVector_continuous (X T : ℝ) :
    Continuous (pairZeroWindowVector X T) := by sorry

theorem pairZeroMeanSquare_eq_full (X T : ℝ) (hX : 1 ≤ X) :
    pairZeroMeanSquare X T = 4*∫ t in (0:ℝ)..T, ‖pairZeroFullVector X t‖^2 := by sorry

theorem pairZeroVector_product (i j : ZeroOccurrence) (X t : ℝ) :
    pairZeroVector i X t * star (pairZeroVector j X t) =
      Complex.exp ((Real.log X : ℂ)*(occurrenceValue i+star (occurrenceValue j)-1)) *
        pairKernelProduct (occurrenceOrdinate i-occurrenceOrdinate j)
          (occurrenceDisplacement i) (-occurrenceDisplacement j) (t-occurrenceOrdinate j) := by sorry

theorem pairZeroVector_product_integrable (i j : ZeroOccurrence) (X : ℝ) :
    Integrable (fun t => pairZeroVector i X t * star (pairZeroVector j X t)) := by sorry

theorem pairZeroVector_product_integral (i j : ZeroOccurrence) (X : ℝ) :
    (∫ t : ℝ, pairZeroVector i X t * star (pairZeroVector j X t)) =
      Complex.exp ((Real.log X : ℂ)*(occurrenceValue i+star (occurrenceValue j)-1)) *
        (2*Real.pi/(4-(occurrenceValue i+star (occurrenceValue j)-1)^2)) := by sorry

theorem pairZero_finite_square (s : Finset ZeroOccurrence) (X t : ℝ) :
    ((‖∑ i ∈ s, pairZeroVector i X t‖^2 : ℝ):ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, pairZeroVector i X t * star (pairZeroVector j X t) := by sorry

theorem pairZeroWindow_square_integrable (X T : ℝ) :
    Integrable (fun t => ‖pairZeroWindowVector X T t‖^2) := by sorry

theorem pairZeroWindow_reflection (T : ℝ) (i : ZeroOccurrence) :
    occurrenceReflection i ∈ occurrenceWindow 0 T ↔ i ∈ occurrenceWindow 0 T := by sorry

theorem pairCorrelationSum_norm (X T : ℝ) (_hX : 0 < X) :
    pairCorrelationSum X T = ((2/Real.pi * ∫ t : ℝ, ‖pairZeroWindowVector X T t‖^2 : ℝ):ℂ) := by sorry

theorem pairCorrelationSum_im (X T : ℝ) (hX : 0 < X) : (pairCorrelationSum X T).im = 0 := by sorry

theorem pairCorrelationSum_re_nonneg (X T : ℝ) (hX : 0 < X) :
    0 ≤ (pairCorrelationSum X T).re := by sorry

theorem pairZero_errors_integrable (X T Z : ℝ) (hX : 1 ≤ X) :
    IntervalIntegrable (fun t => ‖pairZeroFullVector X t‖^2-‖pairZeroCutoffVector X Z t‖^2) volume 0 T ∧
    IntervalIntegrable (fun t => ‖pairZeroCutoffVector X Z t‖^2-‖pairZeroWindowVector X T t‖^2) volume 0 T ∧
    IntegrableOn (fun t => ‖pairZeroWindowVector X T t‖^2) (Set.Icc (0:ℝ) T)ᶜ := by sorry

theorem pairZero_norm_normalization (X T : ℝ) (hX : 0 < X) :
    2*Real.pi*(pairCorrelationSum X T).re = 4*∫ t : ℝ, ‖pairZeroWindowVector X T t‖^2 := by sorry

theorem pairZero_window_integral_split (X T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ, ‖pairZeroWindowVector X T t‖^2) =
      (∫ t in (0:ℝ)..T, ‖pairZeroWindowVector X T t‖^2) +
      ∫ t in (Set.Icc (0:ℝ) T)ᶜ, ‖pairZeroWindowVector X T t‖^2 := by sorry

theorem pairZeroExtensionError_nonpos (X T : ℝ) : pairZeroExtensionError X T ≤ 0 := by sorry

theorem pairZero_decomposition (X T Z : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) (_hZ : 0 ≤ Z) :
    pairZeroMeanSquare X T = 2*Real.pi*(pairCorrelationSum X T).re +
      pairZeroTruncError X T Z + pairZeroHeightError X T Z + pairZeroExtensionError X T := by sorry

theorem pairZero_decomposition_manuscript (X T Z : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hZ : 2*T ≤ Z) :
    pairZeroMeanSquare X T = 2*Real.pi*(pairCorrelationSum X T).re +
      pairZeroTruncError X T Z + pairZeroHeightError X T Z + pairZeroExtensionError X T := by sorry

theorem pairZero_decomposition_unit (T Z : ℝ) (hT : 0 ≤ T) (hZ : 0 ≤ Z) :
    pairZeroMeanSquare 1 T = 2*Real.pi*(pairCorrelationSum 1 T).re +
      pairZeroTruncError 1 T Z + pairZeroHeightError 1 T Z + pairZeroExtensionError 1 T := by sorry

theorem pairZero_empty_window (X T : ℝ) (h : occurrenceWindow 0 T = ∅) :
    pairZeroWindowVector X T = 0 ∧ pairCorrelationSum X T = 0 ∧ pairZeroExtensionError X T = 0 := by sorry

theorem pairZero_height_zero (X Z : ℝ) :
    pairZeroMeanSquare X 0 = 0 ∧ pairCorrelationSum X 0 = 0 ∧
    pairZeroTruncError X 0 Z = 0 ∧ pairZeroHeightError X 0 Z = 0 ∧ pairZeroExtensionError X 0 = 0 := by sorry

end
end HigherCorrelations
