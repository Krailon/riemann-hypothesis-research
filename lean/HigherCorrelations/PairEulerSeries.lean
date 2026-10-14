import HigherCorrelations.PairExactDefinitions
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! The absolutely convergent Euler logarithmic derivative in the exact pair conventions.
UNCONDITIONAL. n indexes the positive integer n+1, including the zero Λ(1) term. -/
namespace HigherCorrelations
noncomputable section

theorem pairEulerTerm_eq_LSeries (n : ℕ) (z : ℂ) :
    pairEulerTerm n z =
      LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) z (n+1) := by
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
  unfold pairEulerTerm
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Nat.succ_ne_zero n))]
  have hl : Complex.log ((n+1:ℕ):ℂ) = (Real.log (n+1:ℝ):ℂ) := by
    simpa using (Complex.ofReal_log (by positivity : 0 ≤ (n+1:ℝ))).symm
  rw [hl, mul_neg, Complex.exp_neg, div_eq_mul_inv]

theorem pairEulerTerm_summable (z : ℂ) (hz : 1 < z.re) :
    Summable (fun n => pairEulerTerm n z) := by
  simp_rw [pairEulerTerm_eq_LSeries]
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hz).comp_injective
    (fun a b h => Nat.add_right_cancel h)

theorem pairEulerSeries (z : ℂ) (hz : 1 < z.re) :
    (∑' n, pairEulerTerm n z) = -deriv riemannZeta z / riemannZeta z := by
  simp_rw [pairEulerTerm_eq_LSeries]
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz]
  unfold LSeries
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hz).tsum_eq_zero_add
  simpa using h.symm

theorem pairEulerTerm_norm (n : ℕ) (z : ℂ) :
    ‖pairEulerTerm n z‖ = ArithmeticFunction.vonMangoldt (n+1) /
      (n+1 : ℝ)^z.re := by
  rw [pairEulerTerm_eq_LSeries, LSeries.norm_term_eq]
  simp [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

theorem pairEulerTerm_norm_vertical (n : ℕ) (σ v : ℝ) :
    ‖pairEulerTerm n ((σ:ℂ)+(v:ℂ)*Complex.I)‖ = ‖pairEulerTerm n σ‖ := by
  simp only [pairEulerTerm_norm, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

end
end HigherCorrelations
