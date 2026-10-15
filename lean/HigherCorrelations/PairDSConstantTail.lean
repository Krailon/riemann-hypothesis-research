import HigherCorrelations.PairElementaryErrorBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! UNCONDITIONAL effective approximation of C_DS. A deliberately simple
16 N^(-1/4) tail certifies effectiveness without optimizing the constant. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem pairDS_term_majorant (n : ℕ) (hn : 0 < n) :
    ArithmeticFunction.vonMangoldt n / (n:ℝ)^(3/2:ℝ) ≤ 4*(n:ℝ)^(-5/4:ℝ) := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hlog := Real.log_le_rpow_div hp.le (show (0:ℝ) < 1/4 by norm_num)
  calc
    _ ≤ (4*(n:ℝ)^(1/4:ℝ))/(n:ℝ)^(3/2:ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := ArithmeticFunction.vonMangoldt_le_log (n := n)
      linarith
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub hp]
      norm_num

theorem pairDS_tail_bound (N : ℕ) (hN : 1 ≤ N) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt (n+N+1) /
      (n+N+1:ℝ)^(3/2:ℝ) ≤ 16*(N:ℝ)^(-1/4:ℝ) := by
  have hp : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hs : Summable (fun n : ℕ => (n+N+1:ℝ)^(-5/4:ℝ)) := by
    have h := (Real.summable_nat_rpow.mpr (show (-5/4:ℝ) < -1 by norm_num)).comp_injective
      (fun a b (h : a+N+1=b+N+1) => by omega)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have hds : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt (n+N+1) /
      (n+N+1:ℝ)^(3/2:ℝ)) := by
    have h := pairDSConstant_summable.comp_injective
      (fun a b (h : a+N=b+N) => Nat.add_right_cancel h)
    simpa only [Function.comp_def, Nat.cast_add] using h
  have hi : AntitoneOn (fun x : ℝ => x^(-5/4:ℝ)) (Ici (N:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hp.trans_le hx) hxy (by norm_num)
  have hb := hi.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt (show (-5/4:ℝ) < -1 by norm_num) hp)
    (fun x hx => Real.rpow_nonneg (hp.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (show (-5/4:ℝ) < -1 by norm_num) hp] at hb
  norm_num only [show (-5/4:ℝ)+1 = -1/4 by norm_num, Nat.cast_add, Nat.cast_one] at hb
  calc
    _ ≤ ∑' n : ℕ, 4*(n+N+1:ℝ)^(-5/4:ℝ) :=
      hds.tsum_le_tsum (fun n => by
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
          pairDS_term_majorant (n+N+1) (by omega)) (hs.mul_left 4)
    _ = 4 * ∑' n : ℕ, (n+N+1:ℝ)^(-5/4:ℝ) := tsum_mul_left
    _ ≤ 16*(N:ℝ)^(-1/4:ℝ) := by linarith

theorem pairDSConstant_approximation (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ pairDSConstant - ∑ n ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt (n+1)/(n+1:ℝ)^(3/2:ℝ) ∧
    pairDSConstant - ∑ n ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt (n+1)/(n+1:ℝ)^(3/2:ℝ) ≤ 16*(N:ℝ)^(-1/4:ℝ) := by
  have he := pairDSConstant_summable.sum_add_tsum_nat_add N
  change _ = pairDSConstant at he
  have ht : pairDSConstant - ∑ n ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt (n+1)/(n+1:ℝ)^(3/2:ℝ) =
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt (n+N+1)/(n+N+1:ℝ)^(3/2:ℝ) := by
    simpa only [Function.comp_def, Nat.cast_add] using (eq_sub_of_add_eq' he).symm
  rw [ht]
  exact ⟨tsum_nonneg (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)),
    pairDS_tail_bound N hN⟩

end
end HigherCorrelations
