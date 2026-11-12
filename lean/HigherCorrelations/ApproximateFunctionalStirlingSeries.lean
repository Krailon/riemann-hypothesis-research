import HigherCorrelations.ApproximateFunctionalStirlingStep
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! UNCONDITIONAL absolute convergence and a uniform horizontal-tail bound
for the logarithmic Stirling correction series. -/
namespace HigherCorrelations
noncomputable section
open Complex Filter
open scoped Topology

theorem afe_shift_norm (z : ℂ) (hz : 0 ≤ z.re) (u : ℝ) (hu : 0 ≤ u) :
    ‖z‖ ≤ ‖z+u‖ ∧ (‖z‖+u)^2 ≤ 2*‖z+u‖^2 := by
  have hs := Complex.sq_norm z
  have ht := Complex.sq_norm (z+u)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, add_zero] at hs ht
  constructor
  · nlinarith [mul_nonneg hz hu, norm_nonneg z, norm_nonneg (z+u), sq_nonneg u]
  · nlinarith [sq_nonneg (‖z‖-u), mul_nonneg hz hu]

theorem afeStirlingStep_shift_bound (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) (n : ℕ) :
    ‖afeStirlingStep (z+n)‖ ≤ 8*((‖z‖+(n:ℝ))⁻¹-(‖z‖+(n:ℝ)+1)⁻¹) := by
  have h := afe_shift_norm z hz n (Nat.cast_nonneg n)
  norm_cast at h
  have hp : 0 < ‖z‖+(n:ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hnp : 0 < ‖z+(n:ℂ)‖ := by linarith [h.1]
  have hbase := afeStirlingStep_bound (z+n) (hnorm.trans h.1)
  apply hbase.trans
  calc
    _ ≤ 4/(‖z‖+(n:ℝ))^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hnp) (sq_pos_of_pos hp)).mpr
      nlinarith [h.2]
    _ ≤ _ := by
      have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
      have he : (‖z‖+(n:ℝ))⁻¹-(‖z‖+(n:ℝ)+1)⁻¹ =
          1/((‖z‖+(n:ℝ))*(‖z‖+(n:ℝ)+1)) := by field_simp; ring
      rw [he, ← mul_div_assoc, mul_one]
      apply (div_le_div_iff₀ (sq_pos_of_pos hp) (mul_pos hp (by linarith))).mpr
      nlinarith [sq_nonneg (‖z‖+(n:ℝ)-1)]

theorem afe_inverse_differences_hasSum (a : ℝ) (ha : 0 < a) :
    HasSum (fun n : ℕ => (a+(n:ℝ))⁻¹-(a+(n:ℝ)+1)⁻¹) a⁻¹ := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => ?_) _).mpr
  · have ht : Tendsto (fun n : ℕ => (a+(n:ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop)
    have he (N : ℕ) : (∑ n ∈ Finset.range N, ((a+(n:ℝ))⁻¹-(a+(n:ℝ)+1)⁻¹)) =
        a⁻¹-(a+(N:ℝ))⁻¹ := by
      have hh := Finset.sum_range_sub' (fun n : ℕ => (a+(n:ℝ))⁻¹) N
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hh
    simp only [he]
    simpa using tendsto_const_nhds.sub ht
  · apply sub_nonneg.mpr
    exact inv_anti₀ (by positivity) (by linarith)

theorem afeStirlingStep_summable_norm (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) :
    Summable (fun n : ℕ => ‖afeStirlingStep (z+n)‖) := by
  have h := (afe_inverse_differences_hasSum ‖z‖ (by linarith)).summable.mul_left 8
  exact h.of_nonneg_of_le (fun _ => norm_nonneg _) (afeStirlingStep_shift_bound z hz hnorm)

theorem afeStirlingCorrection_bound (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) :
    ‖afeStirlingCorrection z‖ ≤ 8/‖z‖ := by
  have h := (afe_inverse_differences_hasSum ‖z‖ (by linarith)).mul_left 8
  have hs := afeStirlingStep_summable_norm z hz hnorm
  unfold afeStirlingCorrection
  apply (norm_tsum_le_tsum_norm hs).trans
  rw [div_eq_mul_inv, ← h.tsum_eq]
  exact hs.tsum_le_tsum (afeStirlingStep_shift_bound z hz hnorm) h.summable

theorem afeStirlingCorrection_tail (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) (N : ℕ) :
    ‖afeStirlingCorrection z - ∑ n ∈ Finset.range N, afeStirlingStep (z+n)‖ ≤
      8/‖z+N‖ := by
  have hs := (afeStirlingStep_summable_norm z hz hnorm).of_norm
  have he := hs.sum_add_tsum_nat_add N
  have he' : afeStirlingCorrection z - ∑ n ∈ Finset.range N, afeStirlingStep (z+n) =
      afeStirlingCorrection (z+N) := by
    unfold afeStirlingCorrection
    rw [← he]
    simp only [add_sub_cancel_left]
    apply tsum_congr
    intro n
    congr 1
    push_cast; ring
  rw [he']
  apply afeStirlingCorrection_bound
  · simp only [add_re, natCast_re]; positivity
  · exact hnorm.trans (afe_shift_norm z hz N (Nat.cast_nonneg N)).1

theorem afeStirlingCorrection_succ (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) :
    afeStirlingCorrection z = afeStirlingStep z + afeStirlingCorrection (z+1) := by
  have hs := (afeStirlingStep_summable_norm z hz hnorm).of_norm
  have h := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, add_zero] at h
  unfold afeStirlingCorrection
  rw [← h]
  congr 1
  apply tsum_congr
  intro n
  congr 1
  push_cast; ring

end
end HigherCorrelations
