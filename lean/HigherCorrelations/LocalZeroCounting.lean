import HigherCorrelations.LocalJensenBound
import HigherCorrelations.LocalOccurrenceIntervals

/-! UNCONDITIONAL logarithmic local counts, retaining every endpoint multiplicity. -/
namespace HigherCorrelations
noncomputable section
open Metric Complex

theorem right_interval_in_jensen_disk (v : ℝ) (ρ : StripZero)
    (hρ : ρ ∈ rightStripZeroInterval v (v+1)) :
    ρ.val ∈ closedBall (jensenCenter (v+1/2)) (8/5) := by
  rcases (rightStripZeroInterval_mem v (v+1) ρ).mp hρ with ⟨hl,hu,hr⟩
  have hr' := ρ.property.2.2
  change dist ρ.val (jensenCenter (v+1/2)) ≤ 8/5
  rw [dist_eq_norm]
  have hn := Complex.sq_norm (ρ.val-jensenCenter (v+1/2))
  simp [jensenCenter, Complex.normSq_apply] at hn
  dsimp [jensenCenter]
  norm_num at hn ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr'.le),
    mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)]

theorem right_interval_mass_le_jensen (v : ℝ) (hv : 4 ≤ |v+1/2|) :
    (∑ ρ ∈ rightStripZeroInterval v (v+1), (zeroMultiplicity ρ : ℝ)) ≤
      localJensenMass (v+1/2) := by
  classical
  let c := jensenCenter (v+1/2)
  let D := MeromorphicOn.divisor riemannZeta (closedBall c (8/5))
  let S := rightStripZeroInterval v (v+1)
  have ha : AnalyticOnNhd ℂ riemannZeta (closedBall c (8/5)) :=
    (jensen_disk_analytic (v+1/2) hv).mono (closedBall_subset_closedBall (by norm_num))
  have hD : 0 ≤ D := MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha
  have he (ρ : StripZero) (hρ : ρ ∈ S) : D ρ.val = (zeroMultiplicity ρ : ℤ) := by
    rw [MeromorphicOn.divisor_apply ha.meromorphicOn (right_interval_in_jensen_disk v ρ hρ)]
    exact (zeroMultiplicity_order ρ).symm
  have hfin := D.finiteSupport (isCompact_closedBall c (8/5))
  let F := hfin.toFinset
  have hsub : S.image (fun ρ => ρ.val) ⊆ F := by
    intro z hz
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hz
    apply hfin.mem_toFinset.mpr
    change D ρ.val ≠ 0
    rw [he ρ hρ]
    exact_mod_cast (zeroMultiplicity_pos ρ).ne'
  have hh : (∑ ρ ∈ S, (zeroMultiplicity ρ : ℤ)) ≤ ∑ᶠ z, D z := by
    have heq : (∑ ρ ∈ S, (zeroMultiplicity ρ : ℤ)) = ∑ z ∈ S.image (fun ρ => ρ.val), D z := by
      rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
      exact Finset.sum_congr rfl (fun ρ hρ => (he ρ hρ).symm)
    rw [heq, finsum_eq_sum_of_support_subset (s := F) (fun z => D z) (by intro z hz; exact hfin.mem_toFinset.mpr hz)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hD z)
  change (∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ)) ≤ ((∑ᶠ z, D z : ℤ) : ℝ)
  exact_mod_cast hh

theorem occurrence_unit_count_high (v : ℝ) (hv : 4 ≤ |v+1/2|) :
    ((occurrenceInterval v (v+1)).card : ℝ) ≤
      (28 / Real.log (35/32))*Real.log (|v|+2) := by
  have h₁ : ((occurrenceInterval v (v+1)).card : ℝ) ≤
      2 * ∑ ρ ∈ rightStripZeroInterval v (v+1), (zeroMultiplicity ρ : ℝ) := by
    exact_mod_cast occurrenceInterval_card_le_twice_right v (v+1)
  have h₂ := (right_interval_mass_le_jensen v hv).trans (localJensenMass_bound (v+1/2) hv)
  have hd : 0 < Real.log (35/32) := Real.log_pos (by norm_num)
  have ha : |v+1/2|+2 ≤ 2*(|v|+2) := by
    have := abs_add_le v (1/2 : ℝ)
    norm_num at this
    linarith [abs_nonneg v]
  have hl : Real.log (|v+1/2|+2) ≤ 2*Real.log (|v|+2) := by
    have hlog := Real.log_le_log (by positivity) ha
    rw [Real.log_mul (by norm_num) (by positivity)] at hlog
    have ht : Real.log 2 ≤ Real.log (|v|+2) := Real.log_le_log (by norm_num) (by have := abs_nonneg v; linarith)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hl (show 0 ≤ 7 / Real.log (35/32) by positivity)
  calc
    _ ≤ 2*((7 / Real.log (35/32))*(2*Real.log (|v|+2))) := by linarith
    _ = _ := by ring

theorem occurrence_unit_count_low (v : ℝ) (hv : |v+1/2| < 4) :
    (occurrenceInterval v (v+1)).card ≤ (occurrenceCutoff 5).card := by
  apply Finset.card_le_card
  intro i hi
  rcases (mem_occurrenceInterval v (v+1) i).mp hi with ⟨hl,hu⟩
  apply (mem_occurrenceCutoff _ _).mpr
  rcases abs_lt.mp hv with ⟨hv₁,hv₂⟩
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem occurrence_count_local :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ,
      ((occurrenceInterval v (v+1)).card : ℝ) ≤ C*Real.log (|v|+2) := by
  let A : ℝ := 28 / Real.log (35/32)
  let B : ℝ := (occurrenceCutoff 5).card / Real.log 2
  have hA : 0 < A := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A+B, by positivity, fun v => ?_⟩
  have hl : 0 < Real.log (|v|+2) := Real.log_pos (by have := abs_nonneg v; linarith)
  by_cases hv : 4 ≤ |v+1/2|
  · have h := occurrence_unit_count_high v hv
    change _ ≤ A*Real.log (|v|+2) at h
    nlinarith
  · have h : ((occurrenceInterval v (v+1)).card : ℝ) ≤ (occurrenceCutoff 5).card :=
      Nat.cast_le.mpr (occurrence_unit_count_low v (lt_of_not_ge hv))
    have hlog : Real.log 2 ≤ Real.log (|v|+2) := Real.log_le_log (by norm_num) (by have := abs_nonneg v; linarith)
    have he : B*Real.log 2 = (occurrenceCutoff 5).card := by dsimp [B]; field_simp
    nlinarith

end
end HigherCorrelations
