/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from Backlund/ZeroCountCrude.lean at pinned revision
c39a751132c88b6e8080b74c74023fd95b3d8be0: enlarge the subband to Re(s) >= 1/4.
-/
import PrimeNumberTheoremAnd.ZetaBounds
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-! UNCONDITIONAL local growth and nonvanishing estimates for Jensen counting. -/
namespace HigherCorrelations
noncomputable section
open Real Complex Function
open scoped Topology

theorem zeta_norm_le_quarter_strip {z : ℂ} (h1 : 1 / 4 ≤ z.re) (him : 1 ≤ |z.im|) :
    ‖riemannZeta z‖ ≤ 3 + 2 * ‖z‖ := by
  have hzr : (0 : ℝ) < z.re := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at him
    norm_num [Complex.zero_im] at him
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at him
    norm_num [Complex.one_im] at him
  have him1z : (1 : ℝ) ≤ ‖(1 : ℂ) - z‖ := by
    calc (1 : ℝ) ≤ |z.im| := him
      _ = |((1 : ℂ) - z).im| := by
          simp [Complex.sub_im, Complex.one_im]
      _ ≤ ‖(1 : ℂ) - z‖ := Complex.abs_im_le_norm _
  rw [← Zeta0EqZeta one_pos hzr hz1]
  unfold riemannZeta0
  have hA : ‖∑ n ∈ Finset.range (1 + 1), 1 / (n : ℂ) ^ z‖ ≤ 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    push_cast
    rw [Complex.zero_cpow hz0, Complex.one_cpow]
    norm_num
  have hB : ‖(-(((1 : ℕ) : ℂ)) ^ ((1 : ℂ) - z) / (1 - z))‖ ≤ 1 := by
    simp only [Nat.cast_one, Complex.one_cpow, norm_div, norm_neg, norm_one]
    rw [div_le_one (by linarith)]
    exact him1z
  have hC : ‖(-(((1 : ℕ) : ℂ)) ^ (-z) / 2)‖ ≤ 1 / 2 := by
    simp only [Nat.cast_one, Complex.one_cpow, norm_div, norm_neg, norm_one]
    norm_num
  have hI : ‖∫ x in Set.Ioi ((1 : ℕ) : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) /
      (x : ℂ) ^ (z + 1)‖ ≤ 2 := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    have hint : MeasureTheory.IntegrableOn
        (fun x : ℝ ↦ (1 / 2) * x ^ (-z.re - 1)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    have hcmp : (∫ x in Set.Ioi ((1 : ℕ) : ℝ),
        ‖((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (z + 1)‖) ≤
        ∫ x in Set.Ioi (1 : ℝ), (1 / 2) * x ^ (-z.re - 1) := by
      rw [show (((1 : ℕ) : ℝ)) = (1 : ℝ) by norm_num]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg _) hint ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun x hx ↦ ?_)
      rw [Set.mem_Ioi] at hx
      have hx0 : (0 : ℝ) < x := by linarith
      change ‖((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (z + 1)‖ ≤
        1 / 2 * x ^ (-z.re - 1)
      rw [norm_div]
      have hnum : ‖((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ))‖ ≤ 1 / 2 := by
        have hcast : ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) =
            (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
        have hf1 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
        have hf2 : Int.fract x < 1 := Int.fract_lt_one x
        have hfr : (⌊x⌋ : ℝ) + 1 / 2 - x = 1 / 2 - Int.fract x := by
          rw [Int.fract]
          ring
        rw [hfr, abs_le]
        constructor <;> linarith
      have hden : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (z.re + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp [Complex.add_re, Complex.one_re]
      rw [hden, div_eq_mul_inv, ← Real.rpow_neg hx0.le]
      have hexp : -(z.re + 1) = -z.re - 1 := by ring
      rw [hexp]
      exact mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hx0.le _)
    refine hcmp.trans ?_
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      Real.one_rpow]
    have hform : -1 / (-z.re - 1 + 1) = 1 / z.re := by
      rw [show -z.re - 1 + 1 = -z.re by ring, div_neg, neg_div, neg_neg]
    rw [hform]
    have hinv : (1 : ℝ) / z.re ≤ 4 := by
      rw [div_le_iff₀ hzr]
      linarith
    linarith
  calc ‖(∑ n ∈ Finset.range (1 + 1), 1 / (n : ℂ) ^ z) +
        (-(((1 : ℕ) : ℂ)) ^ ((1 : ℂ) - z)) / (1 - z) +
        (-(((1 : ℕ) : ℂ)) ^ (-z)) / 2 +
        z * ∫ x in Set.Ioi ((1 : ℕ) : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) /
          (x : ℂ) ^ (z + 1)‖
      ≤ ‖(∑ n ∈ Finset.range (1 + 1), 1 / (n : ℂ) ^ z) +
          (-(((1 : ℕ) : ℂ)) ^ ((1 : ℂ) - z)) / (1 - z) +
          (-(((1 : ℕ) : ℂ)) ^ (-z)) / 2‖ +
        ‖z * ∫ x in Set.Ioi ((1 : ℕ) : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) /
          (x : ℂ) ^ (z + 1)‖ := norm_add_le _ _
    _ ≤ (‖(∑ n ∈ Finset.range (1 + 1), 1 / (n : ℂ) ^ z) +
          (-(((1 : ℕ) : ℂ)) ^ ((1 : ℂ) - z)) / (1 - z)‖ +
        ‖(-(((1 : ℕ) : ℂ)) ^ (-z)) / 2‖) +
        ‖z‖ * ‖∫ x in Set.Ioi ((1 : ℕ) : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) /
          (x : ℂ) ^ (z + 1)‖ := by
        rw [norm_mul]
        gcongr
        exact norm_add_le _ _
    _ ≤ ((1 + 1) + 1 / 2) + ‖z‖ * 2 := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left hI (norm_nonneg z))
        exact add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hC
    _ ≤ 3 + 2 * ‖z‖ := by linarith [norm_nonneg z]

theorem zeta_line_two_lower (t : ℝ) : (1/4 : ℝ) ≤ ‖riemannZeta (2 + I*t)‖ := by
  let f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ (2 + I*t)
  have hn (n : ℕ) : ‖f n‖ = 1 / ((n : ℝ)+1)^2 := by
    dsimp [f]
    rw [norm_div, norm_one]
    have he : ((n : ℂ)+1) = ((n+1 : ℕ) : ℂ) := by push_cast; ring
    rw [he, norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    norm_num [Real.rpow_natCast]
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^2) := by
    simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)^2) 1).mpr hasSum_zeta_two.summable
  have hnf : Summable (fun n => ‖f n‖) := by simpa only [hn] using hs
  have htail := (summable_nat_add_iff (f := fun n => ‖f n‖) 1).mpr hnf
  have hnorm := norm_tsum_le_tsum_norm htail
  have hf := hnf.of_norm.sum_add_tsum_nat_add 1
  have hr := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  have hz : riemannZeta (2+I*t) = 1 + ∑' n, f (n+1) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp)]
    simpa [f] using hf.symm
  have he : (∑' n, ‖f (n+1)‖) = Real.pi^2/6 - 1 := by
    simp only [hn]
    rw [hasSum_zeta_two.tsum_eq] at hr
    norm_num [Finset.sum_range_succ] at hr
    norm_num [Nat.cast_add, add_assoc]
    linarith

  rw [he] at hnorm
  have ht : ‖(1 : ℂ)‖ ≤ ‖riemannZeta (2+I*t)‖ + ‖∑' n, f (n+1)‖ := by
    calc
      _ = ‖riemannZeta (2+I*t) - ∑' n, f (n+1)‖ := by rw [hz]; simp
      _ ≤ _ := norm_sub_le _ _
  norm_num at ht
  have hp := Real.pi_lt_d2
  have hp0 := Real.pi_pos
  nlinarith

end
end HigherCorrelations
