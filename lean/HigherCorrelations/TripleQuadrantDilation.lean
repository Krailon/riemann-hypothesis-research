import HigherCorrelations.TripleBoundaryTrace

/-! UNCONDITIONAL quadrant dilation and the origin approximate identity.
The Jacobian is b^(-2), without a half-mass convention. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped Pointwise

theorem tripleQuadrant_smul (b : ℝ) (hb : 0<b) : b • tripleQuadrant=tripleQuadrant := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨mul_nonneg hb.le hq.1,mul_nonneg hb.le hq.2⟩
  · intro hp
    refine ⟨(p.1/b,p.2/b),⟨div_nonneg hp.1 hb.le,div_nonneg hp.2 hb.le⟩,?_⟩
    ext <;> simp only [Prod.smul_mk,smul_eq_mul] <;> field_simp

theorem tripleQuadrant_dilation (f : ℝ × ℝ → ℂ) (b : ℝ) (hb : 0<b) :
    (∫ p in tripleQuadrant, f (b*p.1,b*p.2)) =
      ((b^2:ℝ):ℂ)⁻¹*(∫ p in tripleQuadrant, f p) := by
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure (ℝ × ℝ)) f tripleQuadrant hb
  rw [tripleQuadrant_smul b hb] at h
  simpa [Module.finrank_prod,Complex.real_smul,Complex.ofReal_pow,Prod.smul_def,smul_eq_mul] using h

theorem tripleBoundary_origin_substitution (ψ : ℝ × ℝ → ℂ) (b : ℝ) (hb : 0<b) :
    (∫ p in tripleQuadrant, ψ p*(Real.exp (-(2*b*(p.1+p.2))):ℂ)) =
    ((b^2:ℝ):ℂ)⁻¹*(∫ p in tripleQuadrant,
      (Real.exp (-(2*(p.1+p.2))):ℂ)*ψ (p.1/b,p.2/b)) := by
  have h := tripleQuadrant_dilation (fun p =>
    (Real.exp (-(2*(p.1+p.2))):ℂ)*ψ (p.1/b,p.2/b)) b hb
  convert h using 1
  congr 1
  ext p
  simp only [mul_div_cancel_left₀ _ hb.ne']
  rw [mul_comm]
  congr 2
  ring

theorem tripleBoundary_origin_scaled_integrable (ψ : ℝ × ℝ → ℂ)
    (hψ : Continuous ψ) (M b : ℝ) (hb : 0<b)
    (hbound : ∀ p ∈ tripleQuadrant, ‖ψ p‖≤M) :
    IntegrableOn (fun p : ℝ × ℝ =>
      (Real.exp (-(2*(p.1+p.2))):ℂ)*ψ (p.1/b,p.2/b)) tripleQuadrant := by
  have hi := tripleBoundary_origin_kernel_integrable.mul_const M
  apply hi.mono'
  · exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      (Real.exp (-(2*(p.1+p.2))):ℂ)*ψ (p.1/b,p.2/b))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict tripleQuadrant_measurable] with p hp
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hbound (p.1/b,p.2/b)
      ⟨div_nonneg hp.1 hb.le,div_nonneg hp.2 hb.le⟩) (Real.exp_pos _).le

theorem tripleBoundary_origin_approximation (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (M N b : ℝ) (hN : 0≤N) (hb : 0<b)
    (hbound : ∀ p ∈ tripleQuadrant, ‖ψ p‖≤M)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖≤N) :
    ‖(∫ p in tripleQuadrant, (Real.exp (-(2*(p.1+p.2))):ℂ)*ψ (p.1/b,p.2/b))-
      ψ (0,0)/4‖ ≤ N/(4*b) := by
  have hi := tripleBoundary_origin_scaled_integrable ψ hψ.continuous M b hb hbound
  have hj := tripleBoundary_origin_kernel_integrable.ofReal.mul_const (ψ (0,0))
  have he : (∫ p in tripleQuadrant, (Real.exp (-(2*(p.1+p.2))):ℂ)*ψ (0,0))=ψ (0,0)/4 := by
    rw [integral_mul_const,integral_complex_ofReal,tripleBoundary_origin_mass_closed]
    push_cast
    ring
  have hsub : (∫ p in tripleQuadrant,
      (Real.exp (-(2*(p.1+p.2))):ℂ)*(ψ (p.1/b,p.2/b)-ψ (0,0))) =
      (∫ p in tripleQuadrant, (Real.exp (-(2*(p.1+p.2))):ℂ)*ψ (p.1/b,p.2/b))-
      (∫ p in tripleQuadrant, (Real.exp (-(2*(p.1+p.2))):ℂ)*ψ (0,0)) := by
    convert integral_sub hi hj using 1
    congr 1
    ext p
    simp [mul_sub,mul_comm]
  rw [he] at hsub
  rw [← hsub]
  exact tripleBoundary_origin_trace_integral ψ hψ N b hN hb hD

end
end HigherCorrelations
