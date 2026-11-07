import HigherCorrelations.ConstantKernelReflection
import HigherCorrelations.ProfileCriticalExpansion

/-! UNCONDITIONAL pointwise replacement on the full closed horizontal cube.
The numerical constant is deliberately conservative. No zero-density or
summed-error statement is used or asserted. -/
namespace HigherCorrelations
noncomputable section

theorem constantKernel_real_gap_bound (a d : ℝ) (hg : a^2+d^2 ≤ 1) :
    ‖rationalProfile a d 0 0 0-kernelBenchmark‖ ≤ 4*Real.pi*(a^2+d^2) := by
  let g := a^2+d^2
  have hg0 : 0 ≤ g := by dsimp [g]; positivity
  have hg1 : g ≤ 1 := hg
  have hR : 0 ≤ Real.sqrt g := Real.sqrt_nonneg _
  have hR2 : (Real.sqrt g)^2 = g := Real.sq_sqrt hg0
  have ha : |a| ≤ Real.sqrt g := by nlinarith [sq_abs a, sq_nonneg d]
  have hd : |d| ≤ Real.sqrt g := by nlinarith [sq_abs d, sq_nonneg a]
  have hr := rationalProfile_critical_remainder_bound (Real.sqrt g) a d hR ha hd
  have hg2 : g^2 ≤ g := by nlinarith
  have hg3 : g^3 ≤ g := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg2)]
  have hg4 : g^4 ≤ g := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg3)]
  have hc : criticalProfileRemainderConstant (Real.sqrt g) ≤ 3*Real.pi*g := by
    have h4 : (Real.sqrt g)^4 = g^2 := by nlinarith [sq_nonneg ((Real.sqrt g)^2-g)]
    have h6 : (Real.sqrt g)^6 = g^3 := by rw [show (6:ℕ)=2*3 by norm_num, pow_mul, hR2]
    have h8 : (Real.sqrt g)^8 = g^4 := by rw [show (8:ℕ)=2*4 by norm_num, pow_mul, hR2]
    unfold criticalProfileRemainderConstant
    rw [h4, h6, h8]
    nlinarith [mul_le_mul_of_nonneg_left hg2 Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hg3 Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hg4 Real.pi_pos.le]
  have hq := criticalGapQuadratic_nonneg a d
  have hqb : criticalGapQuadratic a d ≤ 3*g/2 := by
    unfold criticalGapQuadratic
    dsimp [g]
    nlinarith [sq_nonneg (a+d)]
  have he : ‖criticalProfileApproximation 1 a d-kernelBenchmark‖ =
      5*Real.pi*criticalGapQuadratic a d/32 := by
    unfold criticalProfileApproximation kernelBenchmark
    have hc : (3*(Real.pi:ℂ)/8)=((3*Real.pi/8:ℝ):ℂ) := by push_cast; ring
    rw [hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    norm_num
    positivity
  have ht := norm_sub_le_norm_sub_add_norm_sub (rationalProfile a d 0 0 0)
    (criticalProfileApproximation 1 a d) kernelBenchmark
  rw [he] at ht
  have hp := mul_le_mul_of_nonneg_left hqb Real.pi_pos.le
  have hpg := mul_nonneg Real.pi_pos.le hg0
  change _ ≤ 4*Real.pi*g
  linarith [hr.trans hc]

theorem constantKernelEmpty_pointwise (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖constantKernelEmpty a d δ-kernelBenchmark‖ ≤
      constantKernelBound*min (constantKernelEnergy a d δ) 1 := by
  have hs : 0 ≤ ∑ j, δ j^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hg : 0 ≤ a^2+d^2 := by positivity
  have hnorm : ‖kernelBenchmark‖ = 3*Real.pi/8 := by
    unfold kernelBenchmark
    rw [norm_div, norm_mul]
    norm_num [abs_of_pos Real.pi_pos]
  by_cases he : constantKernelEnergy a d δ ≤ 1
  · rw [min_eq_left he]
    have hgap : a^2+d^2 ≤ 1 := by unfold constantKernelEnergy at he; linarith
    have ht := norm_sub_le_norm_sub_add_norm_sub (constantKernelEmpty a d δ)
      (rationalProfile a d 0 0 0) kernelBenchmark
    have hh := constantKernelEmpty_horizontal_bound a d δ hδ
    have hr := constantKernel_real_gap_bound a d hgap
    unfold constantKernelBound constantKernelEnergy
    nlinarith [mul_nonneg Real.pi_pos.le hs, mul_nonneg Real.pi_pos.le hg]
  · rw [min_eq_right (le_of_not_ge he)]
    have ht := norm_sub_le (constantKernelEmpty a d δ) kernelBenchmark
    rw [hnorm] at ht
    have hb := constantKernelEmpty_global_bound a d δ hδ
    unfold constantKernelBound
    nlinarith [Real.pi_pos]

theorem constantKernelEmpty_origin : constantKernelEmpty 0 0 0 = kernelBenchmark := by
  have h := constantKernelEmpty_pointwise 0 0 0 (by intro j; norm_num)
  simp only [constantKernelEnergy, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero, min_eq_left (by norm_num : (0:ℝ) ≤ 1),
    mul_zero, norm_le_zero_iff, sub_eq_zero] at h
  exact h

theorem constantKernelEmpty_coincident (a : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖constantKernelEmpty a a δ-kernelBenchmark‖ ≤
      constantKernelBound*min (2*a^2+∑ j, δ j^2) 1 := by
  simpa [constantKernelEnergy, two_mul] using constantKernelEmpty_pointwise a a δ hδ

theorem constantKernelEmpty_cube_endpoints (a d : ℝ) (e : Fin 3 → Bool) :
    ‖constantKernelEmpty a d (fun j => if e j then -(1/2) else 1/2)-kernelBenchmark‖ ≤
      constantKernelBound*min (a^2+d^2+3/4) 1 := by
  have hδ (j : Fin 3) : |if e j then -(1/2:ℝ) else 1/2| ≤ 1/2 := by
    split <;> norm_num
  have hs (j : Fin 3) : (if e j then -(1/2:ℝ) else 1/2)^2 = 1/4 := by
    split <;> norm_num
  have h := constantKernelEmpty_pointwise a d _ hδ
  norm_num [constantKernelEnergy, hs] at h ⊢
  exact h

end
end HigherCorrelations
