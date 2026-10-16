import HigherCorrelations.PairMeanKernelBounds

/-! UNCONDITIONAL lower bound for the boundary kernel, including both
removable points. The sinc-times-argument identity avoids division there. -/
namespace HigherCorrelations
noncomputable section

theorem pairMeanSinc_mul (u : ℝ) : pairMeanSinc u*(Real.pi*u) = Real.sin (Real.pi*u) := by
  by_cases hu : u = 0
  · subst u
    simp
  · rw [pairMeanSinc, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hu)]
    exact div_mul_cancel₀ _ (mul_ne_zero Real.pi_ne_zero hu)

theorem pairMeanB_lower (u : ℝ) : 2/(Real.pi^2*(1+u^2)) ≤ pairMeanB u := by
  have h1 := pairMeanSinc_mul (u/2)
  have h2 := pairMeanSinc_mul ((u-1)/2)
  rw [show Real.pi*((u-1)/2) = Real.pi*(u/2)-Real.pi/2 by ring,
    Real.sin_sub_pi_div_two] at h2
  have hs := Real.sin_sq_add_cos_sq (Real.pi*(u/2))
  have he : pairMeanSinc (u/2)^2*(Real.pi^2*u^2) +
      pairMeanSinc ((u-1)/2)^2*(Real.pi^2*(u-1)^2) = 4 := by
    nlinarith only [hs, congrArg (fun x : ℝ => x^2) h1, congrArg (fun x : ℝ => x^2) h2]
  have hb1 : u^2 ≤ 2*(1+u^2) := by nlinarith [sq_nonneg u]
  have hb2 : (u-1)^2 ≤ 2*(1+u^2) := by nlinarith [sq_nonneg (u+1)]
  have hb := add_le_add
    (mul_le_mul_of_nonneg_left hb1 (mul_nonneg (sq_nonneg (pairMeanSinc (u/2))) (sq_nonneg Real.pi)))
    (mul_le_mul_of_nonneg_left hb2 (mul_nonneg (sq_nonneg (pairMeanSinc ((u-1)/2))) (sq_nonneg Real.pi)))
  apply (div_le_iff₀ (by positivity : 0 < Real.pi^2*(1+u^2))).mpr
  unfold pairMeanB
  nlinarith only [he,hb]

end
end HigherCorrelations
