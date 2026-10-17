import HigherCorrelations.PairDiagonalPowerBall

/-! UNCONDITIONAL. Absolute dyadic summation with a square-root saving. -/
namespace HigherCorrelations
noncomputable section
set_option maxHeartbeats 600000
open scoped ArithmeticFunction.vonMangoldt

theorem pairDiagonalPower_geometric_summable :
    Summable (fun j : ℕ => (j+1:ℝ)^3*(1/4:ℝ)^j) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one 3
    (r := (1/4:ℝ)) (by norm_num)
  have hs := ((summable_nat_add_iff 1).mpr h).mul_left 4
  convert hs using 1
  funext j
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  ring

theorem pairDiagonalPowerBall_double_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun q : ℕ × ℕ => pairDiagonalPowerBall X ((2:ℝ)^q.1*X) q.2) := by
  have hX0 : 0 < X := by linarith
  have hnon (q : ℕ × ℕ) : 0 ≤ pairDiagonalPowerBall X ((2:ℝ)^q.1*X) q.2 :=
    pairDiagonalPowerBall_nonneg _ _ (by positivity) _
  have hg : Summable (fun j : ℕ => ((32/Real.log 2)*pairDiagonalPowerScale X)*
      ((j+1:ℝ)^3*(1/4:ℝ)^j)) := pairDiagonalPower_geometric_summable.mul_left _
  have hr : Summable (fun j : ℕ => ∑' n, pairDiagonalPowerBall X ((2:ℝ)^j*X) n) :=
    Summable.of_nonneg_of_le (fun j => tsum_nonneg (fun n => hnon (j,n)))
      (fun j => pairDiagonalPowerBall_dyadic_bound X hX j) hg
  exact (summable_prod_of_nonneg hnon).mpr
    ⟨fun j => pairDiagonalPowerBall_summable X ((2:ℝ)^j*X),hr⟩

theorem pairDiagonalPowerWeight_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun n : ℕ => if IsPrimePow n ∧ ¬n.Prime then
      pairDiagonalWeight X n*(Λ n)^2 else 0) := by
  apply Summable.of_nonneg_of_le _ _ (pairDiagonalWeight_summable X hX)
  · intro n; split_ifs
    · exact mul_nonneg (pairDiagonalWeight_nonneg _ _ (Nat.cast_nonneg _)) (sq_nonneg _)
    · rfl
  · intro n; split_ifs
    · rfl
    · exact mul_nonneg (pairDiagonalWeight_nonneg _ _ (Nat.cast_nonneg _)) (sq_nonneg _)

theorem pairMeanPrimePowerDiagonal_weight (X : ℝ) (hX : 1 ≤ X) :
    pairMeanPrimePowerDiagonal X = ∑' n : ℕ, if IsPrimePow n ∧ ¬n.Prime then
      pairDiagonalWeight X n*(Λ n)^2 else 0 := by
  rw [(pairDiagonalPowerWeight_summable X hX).tsum_eq_zero_add]
  simp only [ArithmeticFunction.map_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,
    ite_self,zero_add]
  apply tsum_congr
  intro n
  split_ifs
  · simpa only [Nat.cast_add,Nat.cast_one] using pairMeanPrimeCoefficient_sq_weight X hX n
  · rfl

theorem pairMeanPrimePowerDiagonal_sharp : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    pairMeanPrimePowerDiagonal X ≤ C*pairDiagonalPowerScale X := by
  let G := ∑' j : ℕ, (j+1:ℝ)^3*(1/4:ℝ)^j
  have hG : 0 < G := by
    have := pairDiagonalPower_geometric_summable.le_tsum 0 (fun j _ => by positivity)
    simp only [Nat.cast_zero,zero_add,one_pow,pow_zero,mul_one] at this
    dsimp [G]; linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(32/Real.log 2)*G, by positivity, ?_⟩
  intro X hX
  have hX0 : 0 < X := by linarith
  have hd := pairDiagonalPowerBall_double_summable X hX
  have hpoint : ∀ n : ℕ, (if IsPrimePow n ∧ ¬n.Prime then
      pairDiagonalWeight X n*(Λ n)^2 else 0) ≤
      ∑' j : ℕ, pairDiagonalPowerBall X ((2:ℝ)^j*X) n := by
    intro n
    split_ifs with hn
    · obtain ⟨j,hj⟩ := pairDiagonalPowerBall_cover X hX n hn
      exact hj.trans ((hd.prod_symm.prod_factor n).le_tsum j
        (fun k _ => pairDiagonalPowerBall_nonneg _ _ (by positivity) _))
    · exact tsum_nonneg (fun j => pairDiagonalPowerBall_nonneg _ _ (by positivity) _)
  rw [pairMeanPrimePowerDiagonal_weight X hX]
  calc
    _ ≤ ∑' n : ℕ, ∑' j : ℕ, pairDiagonalPowerBall X ((2:ℝ)^j*X) n :=
      (pairDiagonalPowerWeight_summable X hX).tsum_le_tsum hpoint hd.prod_symm.prod
    _ = ∑' j : ℕ, ∑' n : ℕ, pairDiagonalPowerBall X ((2:ℝ)^j*X) n :=
      Summable.tsum_comm (f := fun (j n : ℕ) => pairDiagonalPowerBall X ((2:ℝ)^j*X) n) hd
    _ ≤ ∑' j : ℕ, ((32/Real.log 2)*pairDiagonalPowerScale X)*((j+1:ℝ)^3*(1/4:ℝ)^j) :=
      hd.prod.tsum_le_tsum (pairDiagonalPowerBall_dyadic_bound X hX)
        (pairDiagonalPower_geometric_summable.mul_left _)
    _ = _ := by rw [tsum_mul_left]; dsimp [G]; ring

theorem pairDiagonalPowerScale_bound (X : ℝ) (hX : 1 ≤ X) :
    pairDiagonalPowerScale X ≤ 432 := by
  have hX0 : 0 < X := by linarith
  have hw0 : 0 < 2*X := by positivity
  have hl0 : 0 ≤ Real.log (2*X) := Real.log_nonneg (by linarith)
  have hl : Real.log (2*X) ≤ 6*(2*X)^(1/6:ℝ) := by
    have := Real.log_le_rpow_div hw0.le (show (0:ℝ)<1/6 by norm_num)
    linarith
  have hc : Real.log (2*X)^3 ≤ 216*Real.sqrt (2*X) := by
    have he := pow_le_pow_left₀ hl0 hl 3
    rw [mul_pow,← Real.rpow_natCast ((2*X)^(1/6:ℝ)),← Real.rpow_mul hw0.le] at he
    norm_num at he
    simpa only [Real.sqrt_eq_rpow] using he
  have hs : Real.sqrt (2*X) ≤ 2*Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_right
      ((Real.sqrt_le_left (by norm_num : (0:ℝ)≤2)).mpr (by norm_num)) (Real.sqrt_nonneg _)
  unfold pairDiagonalPowerScale
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hX0)).mpr
  nlinarith

theorem pairMeanPrimePowerDiagonal_bounded : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    pairMeanPrimePowerDiagonal X ≤ C := by
  obtain ⟨K,hK,hb⟩ := pairMeanPrimePowerDiagonal_sharp
  refine ⟨432*K, by positivity, ?_⟩
  intro X hX
  have := mul_le_mul_of_nonneg_left (pairDiagonalPowerScale_bound X hX) hK.le
  nlinarith [hb X hX]

end
end HigherCorrelations
