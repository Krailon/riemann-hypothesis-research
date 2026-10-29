import HigherCorrelations.TripleBoundaryLocalLimits

/-! UNCONDITIONAL scale bounds, including the exact frequency-axis endpoint s=0. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundary_axis_scales (T r s r₀ r₁ S : ℝ) (hT : 2*Real.pi < T)
    (hr₀ : 0 ≤ r₀) (hr : r₀ ≤ r) (hr₁ : r ≤ r₁) (hs : 0 ≤ s) (hS : s ≤ S) :
    1 ≤ (tripleTestBase T)^r ∧ 1 ≤ Real.exp s ∧
    1/((tripleTestBase T)^r*Real.exp s) ≤ (tripleTestBase T)^(-r₀) ∧
    ((tripleTestBase T)^r*Real.exp s)/T ≤ Real.exp S*(tripleTestBase T)^(-(1-r₁)) ∧
    Real.exp (-(2*Real.log (tripleTestBase T)*r)) ≤ (tripleTestBase T)^(-(2*r₀)) := by
  have ht := tripleTestBase_bounds T hT
  have hb : 0 < tripleTestBase T := by linarith [ht.2.1]
  have ht0 : 0 < T := by linarith [ht.1]
  have hx := Real.one_le_rpow ht.2.1.le (hr₀.trans hr)
  have hy := Real.one_le_exp_iff.mpr hs
  refine ⟨hx,hy,?_,?_,?_⟩
  · rw [Real.rpow_neg hb.le,one_div]
    apply (inv_le_inv₀ (by positivity : 0 < (tripleTestBase T)^r*Real.exp s)
      (Real.rpow_pos_of_pos hb r₀)).mpr
    exact (Real.rpow_le_rpow_of_exponent_le ht.2.1.le hr).trans
      (le_mul_of_one_le_right (by positivity) hy)
  · have h1 := div_le_div_of_nonneg_right
      (mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht.2.1.le hr₁) (Real.exp_le_exp.mpr hS)
        (Real.exp_pos s).le (Real.rpow_nonneg hb.le r₁)) ht0.le
    have h2 := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Real.rpow_nonneg hb.le r₁) hb ht.2.2) (Real.exp_pos S).le
    have he : (tripleTestBase T)^r₁/tripleTestBase T=(tripleTestBase T)^(-(1-r₁)) := by
      rw [show -(1-r₁)=r₁-1 by ring,Real.rpow_sub hb,Real.rpow_one]
    rw [he] at h2
    exact h1.trans (by convert h2 using 1 <;> ring)
  · have he : Real.exp (-(2*Real.log (tripleTestBase T)*r))=(tripleTestBase T)^(-(2*r)) := by
      rw [Real.rpow_def_of_pos hb]
      congr 1
      ring
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le ht.2.1.le (by linarith)

end
end HigherCorrelations
