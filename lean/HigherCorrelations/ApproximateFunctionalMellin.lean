import HigherCorrelations.ApproximateFunctionalAlgebra
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! UNCONDITIONAL positive-ray Mellin representation, the starting point for
the sharp-cutoff Hankel contour argument. The interchange uses the exact
integrals of the absolute values, not a formal geometric expansion. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Set

theorem afe_laplace_term (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ))) =
      (1/(n+1:ℂ)^s)*Gamma s := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs
    (by positivity : (0:ℝ)<n+1)
  rw [one_div, inv_cpow_ofReal_nonneg (by positivity)] at h
  simpa only [one_div, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one] using h

theorem afe_laplace_integrable (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun u : ℝ => (u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ))) (Ioi 0) := by
  by_contra h
  have he := afe_laplace_term s hs n
  rw [integral_undef h] at he
  have hn : (n+1:ℂ) ≠ 0 := by exact_mod_cast (show (n:ℝ)+1 ≠ 0 by positivity)
  have hc : (n+1:ℂ)^s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn]
    exact exp_ne_zero _
  exact mul_ne_zero (one_div_ne_zero hc) (Gamma_ne_zero_of_re_pos hs) he.symm

theorem afe_laplace_integral_norm (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    (∫ u : ℝ in Ioi 0, ‖(u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ))‖) =
      (n+1:ℝ)^(-s.re)*Real.Gamma s.re := by
  have he : (∫ u : ℝ in Ioi 0, ‖(u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ))‖) =
      ∫ u : ℝ in Ioi 0, u^(s.re-1)*Real.exp (-((n+1:ℝ)*u)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
    simp
  rw [he, Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by positivity),
    one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

theorem afe_laplace_summable_integral_norm (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ u : ℝ in Ioi 0,
      ‖(u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ))‖) := by
  simp only [afe_laplace_integral_norm s (by linarith)]
  have h := (Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith)).comp_injective
    (show Function.Injective (fun n : ℕ => n+1) by intro a b h; simpa using h)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h.mul_right (Real.Gamma s.re)

theorem afe_exponential_series (u : ℝ) (hu : 0 < u) :
    (∑' n : ℕ, exp (-((n+1:ℝ)*u:ℝ))) = 1/(exp (u:ℂ)-1) := by
  have hnorm : ‖exp (-u:ℂ)‖ < 1 := by
    rw [norm_exp]
    simpa using Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)
  have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_left (exp (-u:ℂ))
  have hterm (n : ℕ) : exp (-u:ℂ)*exp (-u:ℂ)^n = exp (-((n+1:ℝ)*u:ℝ)) := by
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    push_cast; ring
  simp only [hterm] at h
  rw [h.tsum_eq]
  have he : exp (u:ℂ) ≠ 1 := by
    intro he
    have := congrArg norm he
    rw [norm_exp, norm_one] at this
    have hlt : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
    simp only [Complex.ofReal_re] at this
    linarith
  rw [exp_neg]
  field_simp

theorem afe_zeta_mellin (s : ℂ) (hs : 1 < s.re) :
    (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)/(exp (u:ℂ)-1)) = Gamma s * riemannZeta s := by
  have hF := integral_tsum_of_summable_integral_norm
    (fun n => afe_laplace_integrable s (by linarith) n)
    (afe_laplace_summable_integral_norm s hs)
  have he : (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)/(exp (u:ℂ)-1)) =
      ∫ u : ℝ in Ioi 0, ∑' n : ℕ, (u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [tsum_mul_left, afe_exponential_series u hu]
    ring
  rw [he, ← hF]
  simp only [afe_laplace_term s (by linarith)]
  rw [tsum_mul_right, ← zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  ring

theorem afePolynomial_nat_succ (s : ℂ) (m : ℕ) :
    afePolynomial s (m+1:ℕ) = afePolynomial s m + 1/(m+1:ℂ)^s := by
  simp only [afePolynomial, Nat.floor_natCast]
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp only [Nat.cast_add, Nat.cast_one, cpow_neg, one_div]

theorem afePolynomial_range (s : ℂ) (m : ℕ) :
    afePolynomial s m = ∑ n ∈ Finset.range m, 1/(n+1:ℂ)^s := by
  induction m with
  | zero => simp [afePolynomial]
  | succ m ih => rw [afePolynomial_nat_succ, Finset.sum_range_succ, ih]

theorem afe_dirichlet_tail (s : ℂ) (hs : 1 < s.re) (m : ℕ) :
    (∑' n : ℕ, 1/((n+m:ℕ)+1:ℂ)^s) = riemannZeta s - afePolynomial s m := by
  have h : Summable (fun n : ℕ => 1/(n+1:ℂ)^s) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (Complex.summable_one_div_nat_cpow.mpr hs).comp_injective
        (show Function.Injective (fun n : ℕ => n+1) by intro a b h; simpa using h)
  have he := h.sum_add_tsum_nat_add m
  rw [← afePolynomial_range, ← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at he
  linear_combination he

theorem afe_exponential_tail (u : ℝ) (hu : 0 < u) (m : ℕ) :
    (∑' n : ℕ, exp (-(((n+m:ℕ)+1:ℝ)*u:ℝ))) =
      exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by
  have he (n : ℕ) : exp (-(((n+m:ℕ)+1:ℝ)*u:ℝ)) =
      exp (-((m:ℝ)*u:ℝ))*exp (-((n+1:ℝ)*u:ℝ)) := by
    rw [← exp_add]
    congr 1
    push_cast; ring
  simp only [he, tsum_mul_left, afe_exponential_series u hu]
  ring

theorem afe_mellin_tail (s : ℂ) (hs : 1 < s.re) (m : ℕ) :
    (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) =
      Gamma s * (riemannZeta s - afePolynomial s m) := by
  have hsum := (afe_laplace_summable_integral_norm s hs).comp_injective
    (show Function.Injective (fun n : ℕ => n+m) by intro a b h; simpa using h)
  have hF := integral_tsum_of_summable_integral_norm
    (fun n => afe_laplace_integrable s (by linarith) (n+m)) hsum
  have he : (∫ u : ℝ in Ioi 0,
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) =
      ∫ u : ℝ in Ioi 0, ∑' n : ℕ,
        (u:ℂ)^(s-1)*exp (-(((n+m:ℕ)+1:ℝ)*u:ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [tsum_mul_left, afe_exponential_tail u hu m]
    ring
  rw [he, ← hF]
  simp only [afe_laplace_term s (by linarith)]
  rw [tsum_mul_right, afe_dirichlet_tail s hs m]
  ring

theorem afe_zeta_mellin_integrable (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => (u:ℂ)^(s-1)/(exp (u:ℂ)-1)) (Ioi 0) := by
  by_contra h
  have he := afe_zeta_mellin s hs
  rw [integral_undef h] at he
  exact mul_ne_zero (Gamma_ne_zero_of_re_pos (by linarith))
    (riemannZeta_ne_zero_of_one_lt_re hs) he.symm

theorem afe_mellin_tail_integrable (s : ℂ) (hs : 1 < s.re) (m : ℕ) :
    IntegrableOn (fun u : ℝ =>
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) (Ioi 0) := by
  refine Integrable.mono (afe_zeta_mellin_integrable s hs) ?_ ?_
  · have heq : (fun u : ℝ =>
        (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) =
        fun u : ℝ => ((u:ℂ)^(s-1)/(exp (u:ℂ)-1))*exp (-((m:ℝ)*u:ℝ)) := by
      funext u; ring
    rw [heq]
    exact (afe_zeta_mellin_integrable s hs).aestronglyMeasurable.mul
      (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hb : ‖exp (-((m:ℝ)*u:ℝ))‖ ≤ 1 := by
      rw [norm_exp]
      change Real.exp (-((m:ℝ)*u)) ≤ 1
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (mul_nonneg (Nat.cast_nonneg m) (le_of_lt hu)))
    rw [mul_div_right_comm, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hb

end
end HigherCorrelations
