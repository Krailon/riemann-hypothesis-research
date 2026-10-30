import HigherCorrelations.SignedSeriesReflection
import HigherCorrelations.TripleMasterIdentity

/-! UNCONDITIONAL positive-base master bounds, reduced to the checked unit-base kernel. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleMasterCoefficient_positive_bound (X Y : ℝ) (v : MasterTriple) :
    ‖tripleMasterCoefficient X Y v‖ ≤ Real.exp (|Real.log X|+|Real.log Y|) := by
  have hs (x : ℝ) (i j : ZeroOccurrence) :
      ‖Complex.exp ((Real.log x:ℂ)*(occurrenceValue i+star (occurrenceValue j)-1))‖ ≤ Real.exp |Real.log x| := by
    rw [Complex.norm_exp]
    have hreal : (((Real.log x:ℂ)*(occurrenceValue i+star (occurrenceValue j)-1))).re =
        Real.log x*(occurrenceDisplacement i+occurrenceDisplacement j) := by
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
        Complex.add_re,Complex.sub_re,Complex.star_def,Complex.conj_re,Complex.one_re,occurrenceDisplacement]
      ring
    rw [hreal]
    apply Real.exp_le_exp.mpr
    have hi := pair_occurrence_displacement i
    have hj := pair_occurrence_displacement j
    have hh := (abs_add_le (occurrenceDisplacement i) (occurrenceDisplacement j)).trans (add_le_add hi hj)
    have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg (Real.log x))
    have ha := le_abs_self (Real.log x*(occurrenceDisplacement i+occurrenceDisplacement j))
    rw [abs_mul] at ha
    nlinarith only [hm,ha]
  rw [tripleMasterCoefficient,norm_mul,Real.exp_add]
  exact mul_le_mul (hs X _ _) (hs Y _ _) (norm_nonneg _) (Real.exp_pos _).le

theorem tripleMasterTerm_positive_unit (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (v : MasterTriple) (t : ℝ) :
    tripleMasterTerm ω T X Y v t = tripleMasterCoefficient X Y v*tripleMasterTerm ω T 1 1 v t := by
  rw [tripleMasterTerm_eq_kernel ω T X Y hX hY,
    tripleMasterTerm_eq_kernel ω T 1 1 zero_lt_one zero_lt_one]
  simp [tripleMasterCoefficient]
  ring

theorem tripleMasterTerm_positive_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0 < T) (hX : 0 < X) (hY : 0 < Y) (v : MasterTriple) :
    Integrable (tripleMasterTerm ω T X Y v) := by
  change Integrable (fun t => tripleMasterTerm ω T X Y v t)
  simp_rw [tripleMasterTerm_positive_unit ω T X Y hX hY]
  exact (tripleMasterTerm_integrable ω hω hs T 1 1 hT le_rfl le_rfl v).const_mul _

theorem tripleMaster_positive_integralNorm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3 ≤ T) (hX : 0 < X) (hY : 0 < Y) :
    Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) := by
  have hu := tripleMaster_integralNorm_summable ω hω hs T 1 1 hT le_rfl le_rfl
  apply Summable.of_nonneg_of_le (fun v => integral_nonneg (fun t => norm_nonneg _)) _
    (hu.mul_left (Real.exp (|Real.log X|+|Real.log Y|)))
  intro v
  simp_rw [tripleMasterTerm_positive_unit ω T X Y hX hY,norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_right (tripleMasterCoefficient_positive_bound X Y v)
    (integral_nonneg (fun t => norm_nonneg _))

theorem tripleMaster_positive_pointwise_summable (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3 ≤ T) (hX : 0 < X) (hY : 0 < Y) (t : ℝ) :
    Summable (fun v : MasterTriple => ‖tripleMasterTerm ω T X Y v t‖) := by
  have hu := tripleMaster_pointwise_summable ω hs T 1 1 hT le_rfl le_rfl t
  apply Summable.of_nonneg_of_le (fun v => norm_nonneg _) _
    (hu.mul_left (Real.exp (|Real.log X|+|Real.log Y|)))
  intro v
  rw [tripleMasterTerm_positive_unit ω T X Y hX hY,norm_mul]
  exact mul_le_mul_of_nonneg_right (tripleMasterCoefficient_positive_bound X Y v) (norm_nonneg _)

end
end HigherCorrelations
