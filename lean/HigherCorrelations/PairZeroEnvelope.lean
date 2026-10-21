import HigherCorrelations.PairZeroBoundDefinitions
import HigherCorrelations.PairZeroDecomposition

/-! UNCONDITIONAL finite envelope, including reflected occurrences and empty sets. -/
namespace HigherCorrelations
noncomputable section

theorem pairZeroHorizontalEnvelope_nonneg (Z : ℝ) : 0 ≤ pairZeroHorizontalEnvelope Z := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem pairZeroHorizontalEnvelope_lt (Z : ℝ) : pairZeroHorizontalEnvelope Z < 1/2 := by
  classical
  apply (Finset.max'_lt_iff _ _).mpr
  intro d hd
  rcases Finset.mem_insert.mp hd with h|h
  · subst d; norm_num
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    have hz := i.1.property.2.2
    change (occurrenceValue i).re < 1 at hz
    unfold occurrenceDisplacement
    linarith

theorem pairZeroHorizontalEnvelope_member (Z : ℝ) (i : ZeroOccurrence) (hi : i ∈ occurrenceCutoff Z) :
    occurrenceDisplacement i ≤ pairZeroHorizontalEnvelope Z := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,hi,rfl⟩))

theorem pairZeroHorizontalEnvelope_abs (Z : ℝ) (i : ZeroOccurrence) (hi : i ∈ occurrenceCutoff Z) :
    |occurrenceDisplacement i| ≤ pairZeroHorizontalEnvelope Z := by
  have hr : occurrenceReflection i ∈ occurrenceCutoff Z := by
    simpa only [mem_occurrenceCutoff,occurrenceReflection_ordinate] using hi
  have h := pairZeroHorizontalEnvelope_member Z (occurrenceReflection i) hr
  rw [occurrenceReflection_displacement] at h
  exact abs_le.mpr ⟨by linarith,pairZeroHorizontalEnvelope_member Z i hi⟩

theorem pairZeroHorizontalEnvelope_empty (Z : ℝ) (h : occurrenceCutoff Z = ∅) :
    pairZeroHorizontalEnvelope Z = 0 := by
  classical
  simp [pairZeroHorizontalEnvelope,pairZeroHorizontalValues,h]

theorem pairZeroWindow_subset_cutoff (T Z : ℝ) (hT : 0 ≤ T) (hZ : T ≤ Z) :
    occurrenceWindow 0 T ⊆ occurrenceCutoff Z := by
  intro i hi
  rcases (mem_occurrenceWindow 0 T i).mp hi with ⟨ha,hb⟩
  rw [mem_occurrenceCutoff,abs_of_pos ha]
  exact hb.trans hZ

theorem pairZeroVector_envelope (i : ZeroOccurrence) (X b t : ℝ) (hX : 1 ≤ X)
    (hb : occurrenceDisplacement i ≤ b) :
    ‖pairZeroVector i X t‖ ≤ (4/3:ℝ)*X^b*ordinateKernel (t-occurrenceOrdinate i) := by
  have hd := pair_denominator_lower (t-occurrenceOrdinate i) (occurrenceDisplacement i)
    (pair_occurrence_displacement i)
  have hp : 0 < 1+(t-occurrenceOrdinate i)^2 := by positivity
  have hn : 0 < ‖1+((t-occurrenceOrdinate i:ℝ)+Complex.I*occurrenceDisplacement i)^2‖ := by linarith
  have he : Real.exp (Real.log X * occurrenceDisplacement i) ≤ X^b := by
    rw [Real.rpow_def_of_pos (by linarith : 0<X)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb (Real.log_nonneg hX))
  have hnorm : ‖pairZeroVector i X t‖ = Real.exp (Real.log X*occurrenceDisplacement i) /
      ‖1+((t-occurrenceOrdinate i:ℝ)+Complex.I*occurrenceDisplacement i)^2‖ := by
    simp [pairZeroVector,scalarKernel,norm_mul,Complex.norm_exp,div_eq_mul_inv]
  rw [hnorm]
  calc
    _ ≤ X^b/((3/4)*(1+(t-occurrenceOrdinate i)^2)) :=
      div_le_div₀ (by positivity) he (by positivity) hd
    _ = _ := by unfold ordinateKernel; field_simp

theorem pairZeroWeight_square (X b : ℝ) (hX : 0 < X) : (X^b)^2 = X^(2*b) := by
  rw [show 2*b = b+b by ring,Real.rpow_add hX]
  ring

end
end HigherCorrelations
