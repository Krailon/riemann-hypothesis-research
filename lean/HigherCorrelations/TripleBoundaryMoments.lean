import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! UNCONDITIONAL one-sided exponential moments. Integrals over Ioi 0 equal
those over Ici 0: endpoints carry no Lebesgue mass. No half-weight convention. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBoundary_moment_integrable (n : ℕ) (a : ℝ) (ha : 0<a) :
    IntegrableOn (fun s : ℝ => s^n*Real.exp (-(a*s))) (Ioi 0) := by
  simpa only [Real.rpow_natCast,Real.rpow_one,neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (-1:ℝ)<(n:ℝ)) (by norm_num) ha)

theorem tripleBoundary_moment (n : ℕ) (a : ℝ) (ha : 0<a) :
    (∫ s : ℝ in Ioi 0, s^n*Real.exp (-(a*s))) = (n.factorial:ℝ)/(a^(n+1)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1) (by positivity) ha
  have he : (1/a)^((n:ℝ)+1) = (1/a)^(n+1:ℕ) := by
    convert Real.rpow_natCast (1/a) (n+1) using 1 <;> push_cast <;> rfl
  rw [he] at h
  simpa [Real.rpow_natCast,Real.Gamma_nat_eq_factorial,div_pow,div_eq_mul_inv,mul_comm] using h

theorem tripleBoundary_origin_mass :
    (∫ u : ℝ in Ioi 0, Real.exp (-(2*u))) *
      (∫ v : ℝ in Ioi 0, Real.exp (-(2*v))) = (1/4:ℝ) := by
  have h := tripleBoundary_moment 0 2 (by norm_num)
  norm_num at h ⊢
  rw [h]
  norm_num

theorem tripleBoundary_axis_mass :
    (∫ s : ℝ in Ioi 0, (1+s)*Real.exp (-(2*s))) = (3/4:ℝ) := by
  have h0 := tripleBoundary_moment_integrable 0 2 (by norm_num)
  have h1 := tripleBoundary_moment_integrable 1 2 (by norm_num)
  have e0 := tripleBoundary_moment 0 2 (by norm_num)
  have e1 := tripleBoundary_moment 1 2 (by norm_num)
  simp only [pow_zero,one_mul,pow_one] at h0 h1 e0 e1
  simp_rw [add_mul,one_mul]
  rw [integral_add h0 h1,e0,e1]
  norm_num

theorem tripleBoundary_axis_first_moment :
    (∫ s : ℝ in Ioi 0, s*(1+s)*Real.exp (-(2*s))) = (1/2:ℝ) := by
  have h1 := tripleBoundary_moment_integrable 1 2 (by norm_num)
  have h2 := tripleBoundary_moment_integrable 2 2 (by norm_num)
  have e1 := tripleBoundary_moment 1 2 (by norm_num)
  have e2 := tripleBoundary_moment 2 2 (by norm_num)
  simp only [pow_one] at h1 e1
  have he (s : ℝ) : s*(1+s)*Real.exp (-(2*s)) = s*Real.exp (-(2*s))+s^2*Real.exp (-(2*s)) := by ring
  simp_rw [he]
  rw [integral_add h1 h2,e1,e2]
  norm_num

end
end HigherCorrelations
