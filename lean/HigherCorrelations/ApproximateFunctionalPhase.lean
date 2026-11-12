import HigherCorrelations.ApproximateFunctionalDefinitions
import Mathlib.Analysis.Complex.Trigonometric

/-! UNCONDITIONAL normalization and sign checks for the oscillatory factor.
No Gamma asymptotic is used in these exact identities. -/
namespace HigherCorrelations
noncomputable section
open Complex
open scoped ComplexConjugate

theorem afeHeight_nonneg (t : ℝ) : 0 ≤ afeHeight t := by
  unfold afeHeight; positivity

theorem afeHeight_pos {t : ℝ} (ht : t ≠ 0) : 0 < afeHeight t := by
  unfold afeHeight; exact div_pos (abs_pos.mpr ht) (by positivity)

theorem afeHeight_neg (t : ℝ) : afeHeight (-t) = afeHeight t := by
  simp [afeHeight]

theorem afeHeight_ge_one {t : ℝ} (ht : 2*Real.pi ≤ |t|) : 1 ≤ afeHeight t := by
  exact (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr (by simpa using ht)

theorem afePhase_norm (σ t : ℝ) : ‖afePhase σ t‖ = afeHeight t ^ (1/2-σ) := by
  rw [afePhase, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (afeHeight_nonneg t) _)]

theorem afePhase_ne_zero (σ : ℝ) {t : ℝ} (ht : t ≠ 0) : afePhase σ t ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [afePhase_norm]
  exact (Real.rpow_pos_of_pos (afeHeight_pos ht) _).ne'

theorem afePhase_conj (σ t : ℝ) : afePhase σ (-t) = conj (afePhase σ t) := by
  unfold afePhase
  rw [afeHeight_neg]
  simp only [map_mul, conj_ofReal, ← exp_conj, conj_I, map_add, map_neg]
  congr 1
  push_cast
  rw [Left.sign_neg, SignType.coe_neg]
  push_cast
  congr 1
  ring

theorem afePhase_positive (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    afePhase σ t = (afeHeight t ^ (1/2-σ) : ℝ) *
      exp (((-t * Real.log (afeHeight t / Real.exp 1) + Real.pi/4 : ℝ) : ℂ)*I) := by
  simp [afePhase, sign_pos ht]

theorem afePhase_critical_norm (t : ℝ) : ‖afePhase (1/2) t‖ = 1 := by
  rw [afePhase_norm]; norm_num

theorem afePhase_mul_conj (σ t : ℝ) :
    afePhase σ t * afePhase σ (-t) = (afeHeight t ^ (1-2*σ) : ℝ) := by
  rw [afePhase_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, afePhase_norm]
  norm_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (afeHeight_nonneg t)]
  congr 1; ring

end
end HigherCorrelations
