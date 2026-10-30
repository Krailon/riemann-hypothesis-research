import HigherCorrelations.SignedSectorGeometry
import HigherCorrelations.TripleTestPhase

/-! UNCONDITIONAL hexagonal coefficient bound. Collect the anchor displacement
before taking absolute values; separate bounds on the two differences lose support. -/
namespace HigherCorrelations
noncomputable section

theorem signed_horizontal_exponent_bound (p : ℝ × ℝ) (v : MasterTriple) :
    p.1*occurrenceDisplacement (v 0)+p.2*occurrenceDisplacement (v 1)+
      (p.1+p.2)*occurrenceDisplacement (v 2) ≤ signedGauge p := by
  have single (x : ℝ) (i : ZeroOccurrence) : x*occurrenceDisplacement i ≤ |x|/2 := by
    have hh := mul_le_mul_of_nonneg_left (pair_occurrence_displacement i) (abs_nonneg x)
    have h := le_abs_self (x*occurrenceDisplacement i)
    rw [abs_mul] at h
    nlinarith only [h,hh]
  have hh := add_le_add (add_le_add (single p.1 (v 0)) (single p.2 (v 1))) (single (p.1+p.2) (v 2))
  rw [signedGauge_half_sum]
  linarith only [hh]

theorem signed_coefficient_bound (B : ℝ) (hB : 1 < B) (p : ℝ × ℝ) (v : MasterTriple) :
    ‖tripleMasterCoefficient (B^p.1) (B^p.2) v‖ ≤ B^(signedGauge p) := by
  have hb : 0 < B := by linarith
  have hl : 0 ≤ Real.log B := (Real.log_pos hB).le
  rw [tripleMasterCoefficient,norm_mul,Complex.norm_exp,Complex.norm_exp,← Real.exp_add,
    Real.rpow_def_of_pos hb (signedGauge p)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (signed_horizontal_exponent_bound p v) hl
  simp only [Real.log_rpow hb,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.add_re,Complex.sub_re,Complex.star_def,Complex.conj_re,Complex.one_re]
  convert hh using 1 <;> unfold occurrenceDisplacement <;> ring

end
end HigherCorrelations
