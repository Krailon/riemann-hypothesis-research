import HigherCorrelations.TripleQuadrantLeadingDefinitions
import HigherCorrelations.TripleQuadrantDilation
import HigherCorrelations.TripleBoundaryRetained

/-! UNCONDITIONAL exact axis substitution. The transverse Jacobian 1/b
cancels the b from the mixed-prime leading term. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrantAxisKernel_continuous (b : ℝ) : Continuous (tripleQuadrantAxisKernel b) := by
  unfold tripleQuadrantAxisKernel
  fun_prop

theorem tripleBoundary_G_frequency_exact (B : ℝ) (hB : 0<B) (p : ℝ × ℝ) :
    tripleRetainedG (B^p.1) (B^p.2) =
      tripleQuadrantAxisKernel (Real.log B) p+tripleQuadrantAxisKernel (Real.log B) p.swap := by
  rw [Real.rpow_def_of_pos hB,Real.rpow_def_of_pos hB,tripleBoundary_G_exponential]
  dsimp [tripleQuadrantAxisKernel]
  congr 2 <;> congr 1 <;> ring

theorem tripleQuadrantAxisLead_integrable (ψ : ℝ × ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (b : ℝ) :
    IntegrableOn (fun p => ψ p*(tripleQuadrantAxisKernel b p:ℂ)) tripleQuadrant := by
  apply Integrable.integrableOn
  apply Continuous.integrable_of_hasCompactSupport
  · exact hψ.mul (Complex.continuous_ofReal.comp (tripleQuadrantAxisKernel_continuous b))
  · exact hc.mul_right

private theorem integral_Ici_mul_pos (g : ℝ → ℂ) (b : ℝ) (hb : 0<b) :
    (∫ t : ℝ in Ici 0, g (b*t))=(b:ℂ)⁻¹*(∫ t : ℝ in Ici 0, g t) := by
  simp only [integral_Ici_eq_integral_Ioi]
  have h := integral_comp_mul_left_Ioi g 0 hb
  simpa [Complex.real_smul] using h

theorem tripleQuadrantAxis_scaled_integral (ψ : ℝ × ℝ → ℂ) (b r : ℝ) (hb : 0<b) :
    (∫ t : ℝ in Ici 0, ψ (r,t)*(tripleQuadrantAxisKernel b (r,t):ℂ)) =
      tripleQuadrantAxisScaled ψ b r := by
  let g : ℝ → ℂ := fun t => ψ (r,t/b)*(((1+t)*(r+t/(2*b))*Real.exp (-(2*t)):ℝ):ℂ)
  have hbC : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have he (t : ℝ) : ψ (r,t)*(tripleQuadrantAxisKernel b (r,t):ℂ)=(b:ℂ)*g (b*t) := by
    dsimp [g,tripleQuadrantAxisKernel]
    rw [mul_div_cancel_left₀ _ hb.ne']
    push_cast
    field_simp [hbC]
    <;> ring
  simp_rw [he]
  rw [integral_const_mul,integral_Ici_mul_pos g b hb]
  rw [← mul_assoc,mul_inv_cancel₀ hbC,one_mul]
  rfl

theorem tripleQuadrantAxis_substitution (ψ : ℝ × ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (b : ℝ) (hb : 0<b) :
    tripleQuadrantAxisLead ψ b = ∫ r : ℝ in Ici 0, tripleQuadrantAxisScaled ψ b r := by
  have hi := tripleQuadrantAxisLead_integrable ψ hψ hc b
  rw [IntegrableOn,tripleQuadrant_measure] at hi
  unfold tripleQuadrantAxisLead
  rw [tripleQuadrant_measure,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with r
  exact tripleQuadrantAxis_scaled_integral ψ b r hb

end
end HigherCorrelations
