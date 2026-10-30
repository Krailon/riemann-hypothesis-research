import HigherCorrelations.SignedAsymptotic

/-! UNCONDITIONAL signed-frequency and smooth-test assembly.
The open hexagon includes its internal axes and origin. All ordered zero
occurrences and horizontal dependence remain in the exact identity. The
remaining kernel-free complex-argument error is outside this theorem. -/
namespace HigherCorrelations
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap

theorem signed_test_entire (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : Differentiable ℂ (complexFourier φ) :=
  complexFourier_entire φ hφ hc

theorem signed_test_schwartz_inversion (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : ∃ F : 𝓢(FourierPlane,ℂ),
    (∀ x : FourierPlane, F x = complexFourier φ (((planeCoords x).1:ℂ),((planeCoords x).2:ℂ))) ∧
    (∀ ξ : FourierPlane, 𝓕 F ξ = φ (planeCoords ξ)) :=
  complexFourier_schwartz_inversion φ hφ hc

end
end HigherCorrelations
