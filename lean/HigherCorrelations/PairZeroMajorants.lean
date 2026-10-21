import HigherCorrelations.PairZeroEnvelope
import HigherCorrelations.PairKernelEstimates

/-! UNCONDITIONAL weighted kernel estimates. The finite sums retain occurrence
multiplicities, including distinct zeros with a common ordinate. -/
namespace HigherCorrelations
noncomputable section

theorem pairZeroFinite_majorant (s : Finset ZeroOccurrence) (X b t : ℝ)
    (hX : 1 ≤ X) (hb : ∀ i ∈ s, occurrenceDisplacement i ≤ b) :
    ‖∑ i ∈ s, pairZeroVector i X t‖ ≤
      (4/3:ℝ)*X^b * ∑ i ∈ s, ordinateKernel (t-occurrenceOrdinate i) := by
  calc
    _ ≤ ∑ i ∈ s, ‖pairZeroVector i X t‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (4/3:ℝ)*X^b*ordinateKernel (t-occurrenceOrdinate i) :=
      Finset.sum_le_sum (fun i hi => pairZeroVector_envelope i X b t hX (hb i hi))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem pairKernel_finite_le_restricted (s : Finset ZeroOccurrence) (P : ZeroOccurrence → Prop)
    (t : ℝ) (hs : ∀ i ∈ s, P i) :
    (∑ i ∈ s, ordinateKernel (t-occurrenceOrdinate i)) ≤
      ∑' i : {i // P i}, ordinateKernel (t-occurrenceOrdinate i.val) := by
  classical
  have hk := (zeroKernel_summable_bound.choose_spec.2 t).1
  have he : (∑' i : {i // P i}, ordinateKernel (t-occurrenceOrdinate i.val)) =
      ∑' i, Set.indicator {i | P i} (fun i => ordinateKernel (t-occurrenceOrdinate i)) i :=
    tsum_subtype {i | P i} (fun i => ordinateKernel (t-occurrenceOrdinate i))
  rw [he]
  calc
    _ = ∑ i ∈ s, Set.indicator {i | P i} (fun i => ordinateKernel (t-occurrenceOrdinate i)) i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hs i hi]
    _ ≤ _ := (hk.indicator {i | P i}).sum_le_tsum s
      (fun i _ => Set.indicator_nonneg (fun j _ => ordinateKernel_nonneg _) i)

theorem pairZeroFinite_global (s : Finset ZeroOccurrence) (X b t : ℝ)
    (hX : 1 ≤ X) (hb : ∀ i ∈ s, occurrenceDisplacement i ≤ b) :
    ‖∑ i ∈ s, pairZeroVector i X t‖ ≤ (4/3:ℝ)*X^b*zeroKernelSum t := by
  have hk := (zeroKernel_summable_bound.choose_spec.2 t).1
  exact (pairZeroFinite_majorant s X b t hX hb).trans
    (mul_le_mul_of_nonneg_left (hk.sum_le_tsum s (fun i _ => ordinateKernel_nonneg _))
      (by positivity))

theorem pairZeroFull_majorant (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroFullVector X t‖ ≤ (4/3:ℝ)*X^((1:ℝ)/2)*zeroKernelSum t := by
  have hv := pairZeroVector_summable X t hX
  have hk := (zeroKernel_summable_bound.choose_spec.2 t).1
  calc
    _ ≤ ∑' i, ‖pairZeroVector i X t‖ := norm_tsum_le_tsum_norm hv
    _ ≤ ∑' i, (4/3:ℝ)*X^((1:ℝ)/2)*ordinateKernel (t-occurrenceOrdinate i) :=
      hv.tsum_le_tsum (fun i => pairZeroVector_envelope i X (1/2) t hX
        (le_trans (le_abs_self _) (pair_occurrence_displacement i))) (hk.mul_left _)
    _ = _ := tsum_mul_left

theorem pairZeroRemainder_majorant (X Z t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroFullVector X t-pairZeroCutoffVector X Z t‖ ≤
      (4/3:ℝ)*X^((1:ℝ)/2) *
        ∑' i : {i : ZeroOccurrence // Z < |occurrenceOrdinate i|},
          ordinateKernel (t-occurrenceOrdinate i.val) := by
  classical
  have hv := pairZeroVector_summable X t hX
  have hk := (zeroKernel_summable_bound.choose_spec.2 t).1
  have he := hv.of_norm.sum_add_tsum_subtype_compl (occurrenceCutoff Z)
  unfold pairZeroFullVector pairZeroCutoffVector
  rw [← he, add_sub_cancel_left]
  have hp : (fun i : ZeroOccurrence => i ∉ occurrenceCutoff Z) =
      (fun i => Z < |occurrenceOrdinate i|) := by
    funext i
    simp only [mem_occurrenceCutoff,not_le]
  have hn := norm_tsum_le_tsum_norm (hv.subtype (fun i => i ∉ occurrenceCutoff Z))
  rw [hp] at hn ⊢
  calc
    _ ≤ _ := hn
    _ ≤ ∑' i : {i : ZeroOccurrence // Z < |occurrenceOrdinate i|},
        (4/3:ℝ)*X^((1:ℝ)/2)*ordinateKernel (t-occurrenceOrdinate i.val) :=
      (hv.subtype _).tsum_le_tsum (fun i => pairZeroVector_envelope i.val X (1/2) t hX
        (le_trans (le_abs_self _) (pair_occurrence_displacement i.val))) ((hk.subtype _).mul_left _)
    _ = _ := tsum_mul_left

theorem pairZeroCutoff_envelope (X Z t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroCutoffVector X Z t‖ ≤
      (4/3:ℝ)*X^(pairZeroHorizontalEnvelope Z)*zeroKernelSum t :=
  pairZeroFinite_global _ _ _ _ hX (fun i hi => pairZeroHorizontalEnvelope_member Z i hi)

theorem pairZeroWindow_envelope (X T Z t : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) (hZ : T ≤ Z) :
    ‖pairZeroWindowVector X T t‖ ≤
      (4/3:ℝ)*X^(pairZeroHorizontalEnvelope Z)*zeroKernelSum t :=
  pairZeroFinite_global _ _ _ _ hX
    (fun i hi => pairZeroHorizontalEnvelope_member Z i (pairZeroWindow_subset_cutoff T Z hT hZ hi))

theorem pairZeroHeightRemainder_majorant (X T Z t : ℝ)
    (hX : 1 ≤ X) (hT : 0 ≤ T) (hZ : T ≤ Z) :
    ‖pairZeroCutoffVector X Z t-pairZeroWindowVector X T t‖ ≤
      (4/3:ℝ)*X^(pairZeroHorizontalEnvelope Z)*
        ∑' i : {i : ZeroOccurrence // occurrenceOrdinate i ≤ 0 ∨ T < occurrenceOrdinate i},
          ordinateKernel (t-occurrenceOrdinate i.val) := by
  classical
  have hs := pairZeroWindow_subset_cutoff T Z hT hZ
  unfold pairZeroCutoffVector pairZeroWindowVector
  rw [← Finset.sum_sdiff hs, add_sub_cancel_right]
  apply (pairZeroFinite_majorant _ X _ t hX
    (fun i hi => pairZeroHorizontalEnvelope_member Z i (Finset.mem_sdiff.mp hi).1)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pairKernel_finite_le_restricted
  intro i hi
  have hn := (Finset.mem_sdiff.mp hi).2
  simpa only [mem_occurrenceWindow,not_and_or,not_lt,not_le] using hn

theorem pairZeroWindow_exterior_majorant (X T Z t : ℝ)
    (hX : 1 ≤ X) (hT : 0 ≤ T) (hZ : T ≤ Z) :
    ‖pairZeroWindowVector X T t‖ ≤
      (4/3:ℝ)*X^(pairZeroHorizontalEnvelope Z)*
        ∑' i : {i : ZeroOccurrence // 0 < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T},
          ordinateKernel (t-occurrenceOrdinate i.val) := by
  apply (pairZeroFinite_majorant _ X _ t hX
    (fun i hi => pairZeroHorizontalEnvelope_member Z i
      (pairZeroWindow_subset_cutoff T Z hT hZ hi))).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pairKernel_finite_le_restricted _ _ t (fun i hi => (mem_occurrenceWindow 0 T i).mp hi)

end
end HigherCorrelations
