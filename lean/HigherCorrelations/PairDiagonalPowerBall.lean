import HigherCorrelations.PairDiagonalPowerCount

/-! UNCONDITIONAL. Finite dyadic covers of the proper-prime-power diagonal. -/
namespace HigherCorrelations
noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt

theorem pairDiagonalPowerBall_nonneg (X R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    0 ≤ pairDiagonalPowerBall X R n := by
  unfold pairDiagonalPowerBall
  split_ifs <;> positivity

theorem pairDiagonalPowerBall_support (X R : ℝ) (n : ℕ)
    (hn : n ∉ Icc 0 ⌊R⌋₊) : pairDiagonalPowerBall X R n = 0 := by
  unfold pairDiagonalPowerBall
  apply ite_eq_right
  intro h
  exact hn (mem_Icc.mpr ⟨Nat.zero_le _,h.1⟩)

theorem pairDiagonalPowerBall_summable (X R : ℝ) : Summable (pairDiagonalPowerBall X R) :=
  summable_of_ne_finset_zero (pairDiagonalPowerBall_support X R)

theorem pairDiagonalPowerBall_sum (X R : ℝ) :
    (∑' n, pairDiagonalPowerBall X R n) = (8*X^2/R^3)*pairDiagonalPowerCumulative R := by
  rw [tsum_eq_sum (pairDiagonalPowerBall_support X R)]
  unfold pairDiagonalPowerCumulative
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  simp only [pairDiagonalPowerBall, (mem_Icc.mp hn).2, true_and]
  split_ifs <;> simp

theorem pairDiagonalPowerBall_dyadic_bound (X : ℝ) (hX : 1 ≤ X) (j : ℕ) :
    (∑' n, pairDiagonalPowerBall X ((2:ℝ)^j*X) n) ≤
      ((32/Real.log 2)*pairDiagonalPowerScale X)*((j+1:ℝ)^3*(1/4:ℝ)^j) := by
  have hX0 : 0 < X := by linarith
  have hp : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hp0 : 0 < (2:ℝ)^j := by positivity
  have hR : 1 ≤ (2:ℝ)^j*X := one_le_mul_of_one_le_of_one_le hp hX
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 ≤ Real.log (2*X) := Real.log_nonneg (by linarith)
  have hs : Real.sqrt ((2:ℝ)^j*X) ≤ (2:ℝ)^j*Real.sqrt X := by
    rw [Real.sqrt_mul hp0.le]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_left hp0.le).mpr (by nlinarith)
  have hlog : Real.log (2*((2:ℝ)^j*X)) ≤ (j+1:ℝ)*Real.log (2*X) := by
    have he : 2*((2:ℝ)^j*X) = (2:ℝ)^j*(2*X) := by ring
    rw [he,Real.log_mul hp0.ne' (by positivity),Real.log_pow]
    have hlow : Real.log 2 ≤ Real.log (2*X) := Real.log_le_log (by norm_num) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg (α := ℝ) j)]
  have hlog0 : 0 ≤ Real.log (2*((2:ℝ)^j*X)) := Real.log_nonneg (by nlinarith)
  have hb := pairDiagonalPowerCumulative_bound _ hR
  have hbound : pairDiagonalPowerCumulative ((2:ℝ)^j*X) ≤
      (4/Real.log 2)*((2:ℝ)^j*Real.sqrt X)*(((j+1:ℝ)*Real.log (2*X))^3) :=
    hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity))
      (pow_le_pow_left₀ hlog0 hlog 3) (by positivity) (by positivity))
  rw [pairDiagonalPowerBall_sum]
  apply (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 8*X^2/((2:ℝ)^j*X)^3)).trans
  apply le_of_eq
  unfold pairDiagonalPowerScale
  have hsX : (Real.sqrt X)^2 = X := Real.sq_sqrt hX0.le
  have hs0 : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX0).ne'
  have he : (1/4:ℝ)^j = 1/((2:ℝ)^j)^2 := by
    rw [one_div_pow,← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [he]
  field_simp
  rw [hsX]
  ring

theorem pairDiagonalPowerBall_cover (X : ℝ) (hX : 1 ≤ X) (n : ℕ)
    (hn : IsPrimePow n ∧ ¬n.Prime) : ∃ j : ℕ,
    pairDiagonalWeight X n*(Λ n)^2 ≤ pairDiagonalPowerBall X ((2:ℝ)^j*X) n := by
  have hX0 : 0 < X := by linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn.1.ne_zero
  by_cases h : (n:ℝ) ≤ X
  · refine ⟨0, ?_⟩
    simp only [pow_zero,one_mul,pairDiagonalPowerBall,Nat.le_floor h,hn,true_and,ite_true,
      pairDiagonalWeight,h]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (div_le_div_of_nonneg_right h (sq_nonneg X)).trans
    field_simp
    nlinarith
  · obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near
      ((one_le_div hX0).mpr (by linarith : X ≤ (n:ℝ))) (show (1:ℝ)<2 by norm_num)
    have hR : (n:ℝ) ≤ (2:ℝ)^(j+1)*X := ((div_lt_iff₀ hX0).mp hhi).le
    have hRlo : (2:ℝ)^(j+1)*X ≤ 2*(n:ℝ) := by
      have := (le_div_iff₀ hX0).mp hlo
      rw [pow_succ]; nlinarith
    refine ⟨j+1, ?_⟩
    simp only [pairDiagonalPowerBall,Nat.le_floor hR,hn,true_and,ite_true,pairDiagonalWeight,h,ite_false]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hc := pow_le_pow_left₀ (by positivity : 0 ≤ (2:ℝ)^(j+1)*X) hRlo 3
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg X)]

end
end HigherCorrelations
