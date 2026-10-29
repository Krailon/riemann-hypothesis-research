import HigherCorrelations.TripleQuadrantGeometry
import HigherCorrelations.ComplexFourierDecay
import Mathlib.Analysis.Distribution.TemperedDistribution

/-! UNCONDITIONAL distributional inversion for quadrant tests. The amplitude
is represented in L1; no smoothness of its zero extension is used. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped FourierTransform SchwartzMap

private theorem inverse_duality (f : FourierPlane → ℂ) (hf : Integrable f)
    (g : 𝓢(FourierPlane,ℂ)) :
    (∫ x, (𝓕⁻ g) x * f x) = ∫ x, g x * (𝓕⁻ f) x := by
  have he : (-innerₗ FourierPlane).flip = -innerₗ FourierPlane := by
    ext x y
    simp
    ring
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := -innerₗ FourierPlane) Real.continuous_fourierChar
      (continuous_inner.neg) (g.integrable (μ := volume)) hf
  rw [he] at h
  change (∫ x, ((𝓕⁻ g : 𝓢(FourierPlane,ℂ)) : FourierPlane → ℂ) x * f x) = _
  rw [SchwartzMap.fourierInv_coe]
  exact h

theorem tripleQuadrant_distribution (ψ : ℝ × ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ∃ D : 𝓢'(FourierPlane,ℂ),
      (∀ g : 𝓢(FourierPlane,ℂ), D g = ∫ x : FourierPlane,
        g x * tripleQuadrantFourier ψ (((planeCoords x).1:ℂ),((planeCoords x).2:ℂ))) ∧
      (∀ g : 𝓢(FourierPlane,ℂ), (𝓕 D) g = ∫ x : FourierPlane,
        g x * tripleQuadrantAmplitude ψ (planeCoords x)) := by
  let f : FourierPlane → ℂ := fun x => tripleQuadrantAmplitude ψ (planeCoords x)
  have hf : Integrable f := by
    exact (WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_emb
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toHomeomorph.measurableEmbedding |>.mpr
      (tripleQuadrantAmplitude_integrable ψ hψ hc)
  let A : 𝓢'(FourierPlane,ℂ) := (Lp.toTemperedDistribution (hf.toL1 f))
  have hA (g : 𝓢(FourierPlane,ℂ)) : A g = ∫ x, g x*f x := by
    rw [show A g = (Lp.toTemperedDistribution (hf.toL1 f)) g from rfl,Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toL1] with x hx
    change g x * ((hf.toL1 f) x) = g x*f x
    rw [hx]
  refine ⟨𝓕⁻ A,?_,?_⟩
  · intro g
    rw [TemperedDistribution.fourierInv_apply,hA,inverse_duality f hf g]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [tripleQuadrantFourier,complexFourier_real_eq_inverse]
    rfl
  · intro g
    rw [FourierTransform.fourier_fourierInv_eq,hA]

end
end HigherCorrelations
