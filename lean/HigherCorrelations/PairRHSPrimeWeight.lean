import HigherCorrelations.PairMeanEndpoints
import HigherCorrelations.PairDSConstantTail

/-! UNCONDITIONAL absolute weight estimate used after oscillatory integration. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem pairRHS_coefficient_div_log_nonneg (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    0 ≤ pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ) :=
  div_nonneg (pairMeanPrimeCoefficient_nonneg X hX n) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith))

theorem pairRHS_coefficient_div_log_bounds (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ) ≤ Real.sqrt (n+1:ℝ)/X ∧
    pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ) ≤ X*(n+1:ℝ)^(-3/2:ℝ) := by
  have hX0 : 0 < X := by linarith
  have hn : 0 < (n+1:ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (n+1:ℝ) := Real.sqrt_pos.mpr hn
  have hs := Real.sq_sqrt hn.le
  have hb : ArithmeticFunction.vonMangoldt (n+1)/Real.log (n+1:ℝ) ≤ 1 := by
    by_cases hzero : n = 0
    · subst n; simp
    · apply (div_le_one (Real.log_pos (by exact_mod_cast (show 1 < n+1 by omega)))).mpr
      simpa only [Nat.cast_add,Nat.cast_one] using (ArithmeticFunction.vonMangoldt_le_log (n := n+1))
  have he : pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ) =
      (ArithmeticFunction.vonMangoldt (n+1)/Real.log (n+1:ℝ))*
        (1/Real.sqrt (n+1:ℝ))*min ((n+1:ℝ)/X) (X/(n+1:ℝ)) := by
    rw [pairMeanPrimeCoefficient_sqrt]; ring
  have hm : 0 ≤ min ((n+1:ℝ)/X) (X/(n+1:ℝ)) := by positivity
  have hb' : pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ) ≤
      (1/Real.sqrt (n+1:ℝ))*min ((n+1:ℝ)/X) (X/(n+1:ℝ)) := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hb
      (show 0 ≤ (1/Real.sqrt (n+1:ℝ))*min ((n+1:ℝ)/X) (X/(n+1:ℝ)) by positivity)]
  constructor
  · calc
      _ ≤ (1/Real.sqrt (n+1:ℝ))*((n+1:ℝ)/X) := hb'.trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity))
      _ = _ := by field_simp; nlinarith
  · calc
      _ ≤ (1/Real.sqrt (n+1:ℝ))*(X/(n+1:ℝ)) := hb'.trans
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))
      _ = _ := by
        have hr : (n+1:ℝ)^(-3/2:ℝ) = (Real.sqrt (n+1:ℝ)*(n+1:ℝ))⁻¹ := by
          rw [Real.sqrt_eq_rpow,← Real.rpow_add_one hn.ne',← Real.rpow_neg hn.le]
          norm_num
        rw [hr,mul_inv_rev]; ring

theorem pairRHS_coefficient_div_log_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun n : ℕ => pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ)) := by
  have hs : Summable (fun n : ℕ => (n+1:ℝ)^(-3/2:ℝ)) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using (Real.summable_nat_rpow.mpr (by norm_num : (-3/2:ℝ) < -1)).comp_injective
      (fun a b (h : a+1=b+1) => Nat.add_right_cancel h)
  exact Summable.of_nonneg_of_le (pairRHS_coefficient_div_log_nonneg X hX)
    (fun n => (pairRHS_coefficient_div_log_bounds X hX n).2) (hs.mul_left X)

theorem pairRHS_rpow_tail (N : ℕ) (hN : 1 ≤ N) :
    (∑' n : ℕ, (n+N+1:ℝ)^(-3/2:ℝ)) ≤ 2/Real.sqrt N := by
  have hp : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hi : AntitoneOn (fun x : ℝ => x^(-3/2:ℝ)) (Ici (N:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hp.trans_le hx) hxy (by norm_num)
  have hb := hi.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt (show (-3/2:ℝ) < -1 by norm_num) hp)
    (fun x hx => Real.rpow_nonneg (hp.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (show (-3/2:ℝ) < -1 by norm_num) hp] at hb
  have hr : (N:ℝ)^(-3/2+1:ℝ) = (Real.sqrt N)⁻¹ := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_neg hp.le]; norm_num
  norm_num only [Nat.cast_add,Nat.cast_one] at hb
  norm_num at hr
  rw [hr] at hb
  norm_num at hb
  simpa [div_eq_mul_inv,mul_comm] using hb

theorem pairRHS_coefficient_div_log_sum (X : ℝ) (hX : 1 ≤ X) :
    (∑' n : ℕ, pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ)) ≤ 5*Real.sqrt X := by
  let N := Nat.floor X
  have hX0 : 0 < X := by linarith
  have hN : 1 ≤ N := (Nat.le_floor_iff hX0.le).mpr (by simpa using hX)
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNX : (N:ℝ) ≤ X := Nat.floor_le hX0.le
  have hXN : X ≤ 2*N := by
    have h := Nat.lt_floor_add_one X
    have h1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    dsimp [N] at *; linarith
  have hhead : (∑ n ∈ Finset.range N, pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ)) ≤ Real.sqrt X := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, Real.sqrt X/X := by
        apply Finset.sum_le_sum
        intro n hn
        apply (pairRHS_coefficient_div_log_bounds X hX n).1.trans
        gcongr
        have hnN : n+1 ≤ N := by have := Finset.mem_range.mp hn; omega
        exact (show (n+1:ℝ) ≤ N by exact_mod_cast hnN).trans hNX
      _ = (N:ℝ)*Real.sqrt X/X := by simp; ring
      _ ≤ Real.sqrt X := (div_le_iff₀ hX0).mpr (by nlinarith [Real.sqrt_nonneg X])
  have htail : (∑' n : ℕ, pairMeanPrimeCoefficient X (n+N)/Real.log (n+N+1:ℝ)) ≤ 4*Real.sqrt X := by
    have hs := (pairRHS_coefficient_div_log_summable X hX).comp_injective
      (fun a b (h : a+N=b+N) => Nat.add_right_cancel h)
    simp only [Function.comp_def,Nat.cast_add] at hs
    have hr : Summable (fun n : ℕ => (n+N+1:ℝ)^(-3/2:ℝ)) := by
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using (Real.summable_nat_rpow.mpr (by norm_num : (-3/2:ℝ) < -1)).comp_injective
        (fun a b (h : a+N+1=b+N+1) => by omega)
    have hsN : Real.sqrt X ≤ 2*Real.sqrt N := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      rw [mul_pow,Real.sq_sqrt hN0.le]
      nlinarith
    calc
      _ ≤ ∑' n : ℕ, X*(n+N+1:ℝ)^(-3/2:ℝ) := hs.tsum_le_tsum
        (fun n => by simpa only [Nat.cast_add] using (pairRHS_coefficient_div_log_bounds X hX (n+N)).2)
        (hr.mul_left X)
      _ = X*∑' n : ℕ, (n+N+1:ℝ)^(-3/2:ℝ) := tsum_mul_left
      _ ≤ X*(2/Real.sqrt N) := mul_le_mul_of_nonneg_left (pairRHS_rpow_tail N hN) hX0.le
      _ ≤ 4*Real.sqrt X := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (Real.sqrt_pos.mpr hN0)).mpr
        have h := mul_le_mul_of_nonneg_left hsN (Real.sqrt_nonneg X)
        nlinarith [Real.sq_sqrt hX0.le]
  have he := (pairRHS_coefficient_div_log_summable X hX).sum_add_tsum_nat_add N
  have he' : (∑ n ∈ Finset.range N, pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ))+
      (∑' n : ℕ, pairMeanPrimeCoefficient X (n+N)/Real.log (n+N+1:ℝ)) =
        ∑' n : ℕ, pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ) := by
    simpa only [Nat.cast_add] using he
  linarith

end
end HigherCorrelations
