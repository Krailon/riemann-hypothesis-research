import HigherCorrelations.TripleTestGeometry
import HigherCorrelations.ComplexFourierDecay

/-! UNCONDITIONAL phase and coefficient estimates, retaining horizontal sums. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem tripleTest_coefficient_unit (v : MasterTriple) : tripleMasterCoefficient 1 1 v = 1 := by
  simp [tripleMasterCoefficient]

theorem tripleTest_coefficient_bound (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (v : MasterTriple) :
    ‖tripleMasterCoefficient X Y v‖ ≤ X*Y := by
  have single (x : ℝ) (hx : 1 ≤ x) (i j : ZeroOccurrence) :
      ‖Complex.exp ((Real.log x : ℂ)*(occurrenceValue i+star (occurrenceValue j)-1))‖ ≤ x := by
    rw [Complex.norm_exp]
    have hi := i.1.property.2.2
    have hj := j.1.property.2.2
    have hl := Real.log_nonneg hx
    have hr : (occurrenceValue i+star (occurrenceValue j)-1).re ≤ 1 := by
      simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]
      change i.1.val.re+j.1.val.re-1 ≤ 1
      linarith
    calc
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (by simpa using mul_le_mul_of_nonneg_left hr hl)
      _ = x := Real.exp_log (by linarith)
  unfold tripleMasterCoefficient
  rw [norm_mul]
  exact mul_le_mul (single X hX _ _) (single Y hY _ _) (norm_nonneg _) (by linarith)

theorem tripleTest_phase (T : ℝ) (hT : 2*Real.pi < T) (p : ℝ × ℝ) (v : MasterTriple) :
    tripleMasterCoefficient ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) (tripleTestToMaster v) =
    Complex.exp (2*Real.pi*Complex.I*((tripleTestArguments T v).1*p.1+(tripleTestArguments T v).2*p.2)) := by
  have hb : 0 < tripleTestBase T := by linarith [(tripleTestBase_bounds T hT).2.1]
  simp only [tripleMasterCoefficient,Real.log_rpow hb,← Complex.exp_add]
  congr 1
  simp only [tripleTestArguments,complexPair,actualGaps,actualShifts,tripleTestToMaster,
    Equiv.coe_fn_mk,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    occurrenceOrdinate,occurrenceDisplacement]
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.star_def] <;>
    dsimp [meanSpacing,tripleTestBase] <;> field_simp <;> ring

theorem tripleTestFrequencyTerm_integrable (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (T : ℝ)
    (hT : 2*Real.pi < T) (v : MasterTriple) :
    Integrable (tripleTestFrequencyTerm ω φ T v) := by
  change Integrable (fun p => φ p*(8*(tripleMasterCoefficient ((tripleTestBase T)^p.1)
    ((tripleTestBase T)^p.2) (tripleTestToMaster v)*tripleMasterKernel ω T (tripleTestToMaster v))))
  simp_rw [tripleTest_phase T hT]
  apply Continuous.integrable_of_hasCompactSupport
  · exact hφ.continuous.mul (by fun_prop)
  · exact hc.mul_right

theorem tripleTestFrequencyTerm_integral (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ)
    (T : ℝ) (hT : 2*Real.pi < T) (v : MasterTriple) :
    (∫ p, tripleTestFrequencyTerm ω φ T v p) =
      8*(tripleMasterKernel ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v)) := by
  simp only [tripleTestFrequencyTerm,tripleTest_phase T hT]
  unfold complexFourier
  rw [← integral_const_mul,← integral_const_mul]
  congr 1
  funext p
  ring

end
end HigherCorrelations
