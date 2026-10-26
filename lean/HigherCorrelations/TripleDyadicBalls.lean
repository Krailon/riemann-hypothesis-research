import HigherCorrelations.TripleDyadicDefinitions
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Floor.Semiring

/-! UNCONDITIONAL finite balls and summable polynomial-geometric majorants. -/
namespace HigherCorrelations
noncomputable section
open Finset

theorem tripleNatBall_nonneg (R c : ℝ) (hc : 0≤c) (n : ℕ) : 0≤tripleNatBall R c n := by
  unfold tripleNatBall
  split_ifs <;> positivity

theorem tripleNatBall_support (R c : ℝ) (n : ℕ) (hn : n∉Icc 1 ⌊R⌋₊) : tripleNatBall R c n = 0 := by
  unfold tripleNatBall
  apply if_neg
  intro h
  exact hn (mem_Icc.mpr ⟨h.1,Nat.le_floor h.2⟩)

theorem tripleNatBall_summable (R c : ℝ) : Summable (tripleNatBall R c) :=
  summable_of_ne_finset_zero (tripleNatBall_support R c)

theorem tripleNatBall_sum (R c : ℝ) (hR : 0≤R) :
    (∑' n, tripleNatBall R c n) = (⌊R⌋₊:ℝ)*c := by
  rw [tsum_eq_sum (tripleNatBall_support R c)]
  have he : ∀ n ∈ Icc 1 ⌊R⌋₊, tripleNatBall R c n = c := by
    intro n hn
    exact if_pos ⟨(mem_Icc.mp hn).1,(Nat.le_floor_iff hR).mp (mem_Icc.mp hn).2⟩
  simp only [sum_congr rfl he,sum_const,nsmul_eq_mul,Nat.card_Icc]
  simp

theorem tripleNatBall_bound (R c : ℝ) (hR : 0≤R) (hc : 0≤c) :
    (∑' n, tripleNatBall R c n) ≤ R*c := by
  rw [tripleNatBall_sum R c hR]
  exact mul_le_mul_of_nonneg_right (Nat.floor_le hR) hc

theorem tripleDyadic_geometric_summable (k : ℕ) :
    Summable (fun j : ℕ => (1/2:ℝ)^j*(j+2:ℝ)^k) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one k (r := (1/2:ℝ)) (by norm_num)
  have hs := ((summable_nat_add_iff 2).mpr h).mul_left 4
  convert hs using 1
  funext j
  simp only [Nat.cast_add,Nat.cast_ofNat,pow_add]
  ring

theorem tripleDyadicConstant_pos (k : ℕ) : 0<tripleDyadicConstant k := by
  unfold tripleDyadicConstant
  have h : 0≤∑' j : ℕ, (1/2:ℝ)^j*(j+2:ℝ)^k := tsum_nonneg (fun _ => by positivity)
  linarith

theorem tripleDyadicBall_nonneg (x : ℝ) (hx : 1≤x) (k j n : ℕ) :
    0≤tripleDyadicBall x k j n := by
  have hl : 0≤Real.log (2*x) := Real.log_nonneg (by linarith)
  exact tripleNatBall_nonneg _ _ (by positivity) _

theorem tripleDyadicBall_bound (x : ℝ) (hx : 1≤x) (k j : ℕ) :
    (∑' n, tripleDyadicBall x k j n) ≤
      (2*x*Real.log (2*x)^k)*((1/2:ℝ)^j*(j+2:ℝ)^k) := by
  have hl : 0≤Real.log (2*x) := Real.log_nonneg (by linarith)
  apply (tripleNatBall_bound _ _ (by positivity) (by positivity)).trans
  apply le_of_eq
  rw [pow_succ,mul_pow]
  have he : (2:ℝ)^j*(1/4:ℝ)^j=(1/2:ℝ)^j := by rw [← mul_pow]; norm_num
  calc
    _ = 2*x*Real.log (2*x)^k*((2:ℝ)^j*(1/4:ℝ)^j)*(j+2:ℝ)^k := by ring
    _ = _ := by rw [he]; ring

theorem tripleDyadicBall_double_summable (x : ℝ) (hx : 1≤x) (k : ℕ) :
    Summable (fun p : ℕ × ℕ => tripleDyadicBall x k p.1 p.2) := by
  have hr : Summable (fun j => ∑' n, tripleDyadicBall x k j n) :=
    Summable.of_nonneg_of_le (fun j => tsum_nonneg (tripleDyadicBall_nonneg x hx k j))
      (tripleDyadicBall_bound x hx k) ((tripleDyadic_geometric_summable k).mul_left _)
  have hnon (p : ℕ × ℕ) : 0≤tripleDyadicBall x k p.1 p.2 := tripleDyadicBall_nonneg x hx k p.1 p.2
  have hn (j : ℕ) : Summable (fun n => tripleDyadicBall x k j n) := by
    unfold tripleDyadicBall
    exact tripleNatBall_summable _ _
  exact (summable_prod_of_nonneg hnon).mpr ⟨hn,hr⟩

end
end HigherCorrelations
