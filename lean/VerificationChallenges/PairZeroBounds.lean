import HigherCorrelations.PairZeroBoundDefinitions

/-! Independent statement surface; intentional holes occur only in verification challenges. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairZeroHorizontalEnvelope_nonneg (Z : ℝ) : 0 ≤ pairZeroHorizontalEnvelope Z := by sorry

theorem pairZeroHorizontalEnvelope_lt (Z : ℝ) : pairZeroHorizontalEnvelope Z < 1/2 := by sorry

theorem pairZeroHorizontalEnvelope_member (Z : ℝ) (i : ZeroOccurrence) (hi : i ∈ occurrenceCutoff Z) :
    occurrenceDisplacement i ≤ pairZeroHorizontalEnvelope Z := by sorry

theorem pairZeroHorizontalEnvelope_abs (Z : ℝ) (i : ZeroOccurrence) (hi : i ∈ occurrenceCutoff Z) :
    |occurrenceDisplacement i| ≤ pairZeroHorizontalEnvelope Z := by sorry

theorem pairZeroHorizontalEnvelope_empty (Z : ℝ) (h : occurrenceCutoff Z = ∅) :
    pairZeroHorizontalEnvelope Z = 0 := by sorry

theorem pairZeroWindow_subset_cutoff (T Z : ℝ) (hT : 0 ≤ T) (hZ : T ≤ Z) :
    occurrenceWindow 0 T ⊆ occurrenceCutoff Z := by sorry

theorem pairZeroVector_envelope (i : ZeroOccurrence) (X b t : ℝ) (hX : 1 ≤ X)
    (hb : occurrenceDisplacement i ≤ b) :
    ‖pairZeroVector i X t‖ ≤ (4/3:ℝ)*X^b*ordinateKernel (t-occurrenceOrdinate i) := by sorry

theorem pairZeroWeight_square (X b : ℝ) (hX : 0 < X) : (X^b)^2 = X^(2*b) := by sorry

theorem pairZeroFinite_majorant (s : Finset ZeroOccurrence) (X b t : ℝ)
    (hX : 1 ≤ X) (hb : ∀ i ∈ s, occurrenceDisplacement i ≤ b) :
    ‖∑ i ∈ s, pairZeroVector i X t‖ ≤
      (4/3:ℝ)*X^b * ∑ i ∈ s, ordinateKernel (t-occurrenceOrdinate i) := by sorry

theorem pairKernel_finite_le_restricted (s : Finset ZeroOccurrence) (P : ZeroOccurrence → Prop)
    (t : ℝ) (hs : ∀ i ∈ s, P i) :
    (∑ i ∈ s, ordinateKernel (t-occurrenceOrdinate i)) ≤
      ∑' i : {i // P i}, ordinateKernel (t-occurrenceOrdinate i.val) := by sorry

theorem pairZeroFinite_global (s : Finset ZeroOccurrence) (X b t : ℝ)
    (hX : 1 ≤ X) (hb : ∀ i ∈ s, occurrenceDisplacement i ≤ b) :
    ‖∑ i ∈ s, pairZeroVector i X t‖ ≤ (4/3:ℝ)*X^b*zeroKernelSum t := by sorry

theorem pairZeroFull_majorant (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroFullVector X t‖ ≤ (4/3:ℝ)*X^((1:ℝ)/2)*zeroKernelSum t := by sorry

theorem pairZeroRemainder_majorant (X Z t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroFullVector X t-pairZeroCutoffVector X Z t‖ ≤
      (4/3:ℝ)*X^((1:ℝ)/2) *
        ∑' i : {i : ZeroOccurrence // Z < |occurrenceOrdinate i|},
          ordinateKernel (t-occurrenceOrdinate i.val) := by sorry

theorem pairZeroCutoff_envelope (X Z t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroCutoffVector X Z t‖ ≤
      (4/3:ℝ)*X^(pairZeroHorizontalEnvelope Z)*zeroKernelSum t := by sorry

theorem pairZeroWindow_envelope (X T Z t : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) (hZ : T ≤ Z) :
    ‖pairZeroWindowVector X T t‖ ≤
      (4/3:ℝ)*X^(pairZeroHorizontalEnvelope Z)*zeroKernelSum t := by sorry

theorem pairZeroHeightRemainder_majorant (X T Z t : ℝ)
    (hX : 1 ≤ X) (hT : 0 ≤ T) (hZ : T ≤ Z) :
    ‖pairZeroCutoffVector X Z t-pairZeroWindowVector X T t‖ ≤
      (4/3:ℝ)*X^(pairZeroHorizontalEnvelope Z)*
        ∑' i : {i : ZeroOccurrence // occurrenceOrdinate i ≤ 0 ∨ T < occurrenceOrdinate i},
          ordinateKernel (t-occurrenceOrdinate i.val) := by sorry

theorem pairZeroWindow_exterior_majorant (X T Z t : ℝ)
    (hX : 1 ≤ X) (hT : 0 ≤ T) (hZ : T ≤ Z) :
    ‖pairZeroWindowVector X T t‖ ≤
      (4/3:ℝ)*X^(pairZeroHorizontalEnvelope Z)*
        ∑' i : {i : ZeroOccurrence // 0 < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T},
          ordinateKernel (t-occurrenceOrdinate i.val) := by sorry

theorem pairZeroBoundaryProfile_integrable (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (pairZeroBoundaryProfile T) volume 0 T := by sorry

theorem pairZeroBoundaryProfile_integral (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, pairZeroBoundaryProfile T t) = 2*Real.log (1+T) := by sorry

theorem pairZero_tail_profile (a : ℝ) :
    IntegrableOn (fun t : ℝ => (1+t-a)⁻¹^2) (Set.Ioi a) ∧
      (∫ t in Set.Ioi a, (1+t-a)⁻¹^2) = 1 := by sorry

theorem pairZero_left_profile :
    IntegrableOn (fun t : ℝ => (1-t)⁻¹^2) (Set.Iio 0) ∧
      (∫ t in Set.Iio (0:ℝ), (1-t)⁻¹^2) = 1 := by sorry

theorem pairZeroExtensionProfile_left (T t : ℝ) (hT : 0 ≤ T) (ht : t ≤ 0) :
    pairZeroExtensionProfile T t = (1-t)⁻¹^2 := by sorry

theorem pairZeroExtensionProfile_right (T t : ℝ) (hT : 0 ≤ T) (ht : T ≤ t) :
    pairZeroExtensionProfile T t = (1+t-T)⁻¹^2 := by sorry

theorem pairZeroExtensionProfile_integral (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (pairZeroExtensionProfile T) (Set.Icc 0 T)ᶜ ∧
      (∫ t in (Set.Icc (0:ℝ) T)ᶜ, pairZeroExtensionProfile T t) = 2 := by sorry

theorem pairZero_square_difference (u v : ℂ) :
    |‖u‖^2-‖v‖^2| ≤ ‖u-v‖*(‖u‖+‖v‖) := by sorry

theorem pairZero_square_trunc (u v : ℂ) (A R : ℝ)
    (hu : ‖u‖ ≤ A) (hr : ‖u-v‖ ≤ R) :
    |‖u‖^2-‖v‖^2| ≤ 2*A*R+R^2 := by sorry

theorem pairZeroTruncError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
      |pairZeroTruncError X T Z| ≤ C*X*T*
        (Real.log (T+2)*Real.log Z/Z + Real.log Z^2/Z^2) := by sorry

theorem pairZeroHeightError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
      |pairZeroHeightError X T Z| ≤ C*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^3 := by sorry

theorem pairZeroExtensionError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
      |pairZeroExtensionError X T| ≤ C*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^2 := by sorry

theorem pairZeroTruncError_simple_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
      |pairZeroTruncError X T Z| ≤ C*X*T*Real.log Z^2/Z := by sorry

theorem pairZeroUniformBounds :
    ∃ Ctr Ch Ce : ℝ, 0 < Ctr ∧ 0 < Ch ∧ 0 < Ce ∧
      ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*
          (Real.log (T+2)*Real.log Z/Z+Real.log Z^2/Z^2) ∧
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*Real.log Z^2/Z ∧
        |pairZeroHeightError X T Z| ≤ Ch*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^3 ∧
        |pairZeroExtensionError X T| ≤ Ce*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^2 ∧
        pairZeroExtensionError X T ≤ 0 := by sorry

theorem pairZeroEnvelope_monotone_weight (X Z b : ℝ) (hX : 1 ≤ X)
    (hb : pairZeroHorizontalEnvelope Z ≤ b) :
    X^(2*pairZeroHorizontalEnvelope Z) ≤ X^(2*b) := by sorry

theorem pairZeroUniformBounds_envelope :
    ∃ Ctr Ch Ce : ℝ, 0 < Ctr ∧ 0 < Ch ∧ 0 < Ce ∧
      ∀ X T Z b : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z → pairZeroHorizontalEnvelope Z ≤ b →
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*
          (Real.log (T+2)*Real.log Z/Z+Real.log Z^2/Z^2) ∧
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*Real.log Z^2/Z ∧
        |pairZeroHeightError X T Z| ≤ Ch*X^(2*b)*Real.log T^3 ∧
        |pairZeroExtensionError X T| ≤ Ce*X^(2*b)*Real.log T^2 ∧
        pairZeroExtensionError X T ≤ 0 := by sorry

end
end HigherCorrelations
