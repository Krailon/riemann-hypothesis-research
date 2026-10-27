import HigherCorrelations.ComplexFourierDecay
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! UNCONDITIONAL regularity of the compact-frequency inverse transform.
Complex differentiability is joint, with a local compact-support majorant. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff FourierTransform SchwartzMap Topology

private def phaseLinear (p : ℝ × ℝ) : (ℂ × ℂ) →L[ℂ] ℂ :=
  (2*Real.pi*Complex.I*(p.1:ℂ)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
  (2*Real.pi*Complex.I*(p.2:ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ

private theorem phaseLinear_apply (p : ℝ × ℝ) (z : ℂ × ℂ) :
    phaseLinear p z = 2*Real.pi*Complex.I*(z.1*p.1+z.2*p.2) := by
  simp [phaseLinear,smul_eq_mul]
  ring

set_option maxHeartbeats 800000 in
theorem complexFourier_entire (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : Differentiable ℂ (complexFourier φ) := by
  intro z₀
  let F (z : ℂ × ℂ) (p : ℝ × ℝ) := φ p*Complex.exp (phaseLinear p z)
  let D (z : ℂ × ℂ) (p : ℝ × ℝ) := (φ p*Complex.exp (phaseLinear p z)) • phaseLinear p
  have hdiff (z : ℂ × ℂ) (p : ℝ × ℝ) : HasFDerivAt (fun z => F z p) (D z p) z := by
    simpa [F,D,smul_smul,mul_comm,mul_left_comm] using ((phaseLinear p).hasFDerivAt.cexp).const_mul (φ p)
  have hcL : Continuous (fun p : ℝ × ℝ => phaseLinear p) := by unfold phaseLinear; fun_prop
  have hcE : Continuous (fun q : (ℂ × ℂ) × (ℝ × ℝ) => Complex.exp (phaseLinear q.2 q.1)) := by
    simp only [phaseLinear_apply]
    fun_prop
  have hcD : Continuous (fun q : (ℂ × ℂ) × (ℝ × ℝ) => Complex.exp (phaseLinear q.2 q.1) • phaseLinear q.2) :=
    hcE.smul (hcL.comp continuous_snd)
  obtain ⟨M,hM⟩ := ((isCompact_closedBall z₀ 1).prod hc).exists_bound_of_continuousOn hcD.continuousOn
  have hbound : ∀ p, ∀ z ∈ Metric.ball z₀ 1, ‖D z p‖ ≤ ‖φ p‖*max M 0 := by
    intro p z hz
    by_cases hp : p ∈ tsupport φ
    · have hh := hM (z,p) ⟨Metric.ball_subset_closedBall hz,hp⟩
      have he : D z p = φ p • (Complex.exp (phaseLinear p z) • phaseLinear p) := by
        simp [D,smul_smul]
      rw [he,norm_smul]
      exact mul_le_mul_of_nonneg_left (hh.trans (le_max_left _ _)) (norm_nonneg _)
    · have hp0 : φ p=0 := image_eq_zero_of_notMem_tsupport hp
      dsimp only [D]
      rw [norm_smul]
      simp [hp0]
  have hFe (z : ℂ × ℂ) : Continuous (fun p : ℝ × ℝ => Complex.exp (phaseLinear p z)) := by
    simp only [phaseLinear_apply]
    fun_prop
  have hFmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) volume := by
    apply Filter.Eventually.of_forall
    intro z
    change AEStronglyMeasurable (fun p => φ p*Complex.exp (phaseLinear p z)) volume
    exact (hφ.continuous.mul (hFe z)).aestronglyMeasurable
  have hFint : Integrable (F z₀) volume := by
    simpa only [F,phaseLinear_apply] using complexFourier_integrable φ hφ hc z₀
  have hDmeas : AEStronglyMeasurable (D z₀) volume := by
    change AEStronglyMeasurable (fun p => (φ p*Complex.exp (phaseLinear p z₀)) • phaseLinear p) volume
    exact ((hφ.continuous.mul (hFe z₀)).smul hcL).aestronglyMeasurable
  have hbint : Integrable (fun p => ‖φ p‖*max M 0) :=
    (hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hc).norm.mul_const _
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (Metric.ball_mem_nhds z₀ (by norm_num : (0:ℝ) < 1)) hFmeas hFint hDmeas
    (Filter.Eventually.of_forall hbound) hbint (Filter.Eventually.of_forall (fun p z _ => hdiff z p))
  change DifferentiableAt ℂ (fun z => ∫ p : ℝ × ℝ, φ p*Complex.exp (2*Real.pi*Complex.I*(z.1*p.1+z.2*p.2))) z₀
  convert hh.differentiableAt using 1 <;> simp only [F,phaseLinear_apply]

theorem complexFourier_schwartz_inversion (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : ∃ F : 𝓢(FourierPlane,ℂ),
    (∀ x : FourierPlane, F x = complexFourier φ (((planeCoords x).1:ℂ),((planeCoords x).2:ℂ))) ∧
    (∀ ξ : FourierPlane, 𝓕 F ξ = φ (planeCoords ξ)) := by
  have hp : HasCompactSupport (fun ξ : FourierPlane => φ (planeCoords ξ)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (planeCoords.toHomeomorph.isClosedEmbedding.isCompact_preimage hc)
    intro ξ hξ
    exact subset_tsupport φ hξ
  let ψ := hp.toSchwartzMap (hφ.comp planeCoords.contDiff)
  refine ⟨𝓕⁻ ψ,?_,?_⟩
  · intro x
    rw [SchwartzMap.fourierInv_coe,complexFourier_real_eq_inverse]
    rfl
  · intro ξ
    rw [FourierTransform.fourier_fourierInv_eq]
    rfl

end
end HigherCorrelations
