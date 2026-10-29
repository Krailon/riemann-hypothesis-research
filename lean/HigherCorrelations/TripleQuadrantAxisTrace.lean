import HigherCorrelations.TripleQuadrantAxisSubstitution

/-! UNCONDITIONAL axis approximate identity, before the outer trace integral. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

private theorem axis_weight_integrable (b r : ℝ) (hb : 0<b) :
    IntegrableOn (fun t : ℝ => (1+t)*(r+t/(2*b))*Real.exp (-(2*t))) (Ici 0) := by
  have h0 := (tripleBoundary_moment_closed_integrable 0 2 (by norm_num)).const_mul r
  have h1 := (tripleBoundary_moment_closed_integrable 1 2 (by norm_num)).const_mul (r+1/(2*b))
  have h2 := (tripleBoundary_moment_closed_integrable 2 2 (by norm_num)).const_mul (1/(2*b))
  have he : (fun t : ℝ => (1+t)*(r+t/(2*b))*Real.exp (-(2*t))) =
      (((fun t => r*(t^0*Real.exp (-(2*t)))) +
        (fun t => (r+1/(2*b))*(t^1*Real.exp (-(2*t))))) +
        (fun t => (1/(2*b))*(t^2*Real.exp (-(2*t))))) := by
    funext t
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact (h0.add h1).add h2

theorem tripleQuadrantAxisScaled_integrable (ψ : ℝ × ℝ → ℂ) (hψ : Continuous ψ)
    (M b r : ℝ) (hb : 0<b) (hr : 0 ≤ r)
    (hbound : ∀ p ∈ tripleQuadrant, ‖ψ p‖≤M) :
    IntegrableOn (fun t : ℝ =>
      ψ (r,t/b)*(((1+t)*(r+t/(2*b))*Real.exp (-(2*t)):ℝ):ℂ)) (Ici 0) := by
  have hi := (axis_weight_integrable b r hb).const_mul M
  apply hi.mono'
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      ψ (r,t/b)*(((1+t)*(r+t/(2*b))*Real.exp (-(2*t)):ℝ):ℂ))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ici] with t ht
    have ht0 : 0≤t := ht
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0≤(1+t)*(r+t/(2*b))*Real.exp (-(2*t)))]
    exact mul_le_mul_of_nonneg_right (hbound (r,t/b) ⟨hr,div_nonneg ht0 hb.le⟩) (by positivity)

private theorem axis_mass_integrable :
    IntegrableOn (fun t : ℝ => (1+t)*Real.exp (-(2*t))) (Ici 0) := by
  have h := (tripleBoundary_moment_closed_integrable 0 2 (by norm_num)).add
    (tripleBoundary_moment_closed_integrable 1 2 (by norm_num))
  convert h using 1
  ext t
  simp only [Pi.add_apply]
  ring

theorem tripleQuadrantAxis_approximation (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (M N b r : ℝ)
    (hM : 0≤M) (hN : 0≤N) (hb : 0<b) (hr : 0 ≤ r)
    (hbound : ∀ p ∈ tripleQuadrant, ‖ψ p‖≤M)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖≤N) :
    ‖tripleQuadrantAxisScaled ψ b r-(3/4:ℂ)*(r:ℂ)*ψ (r,0)‖≤N*r/(2*b)+M/(4*b) := by
  have hi := tripleQuadrantAxisScaled_integrable ψ hψ.continuous M b r hb hr hbound
  have hj := axis_mass_integrable.ofReal.mul_const ((r:ℂ)*ψ (r,0))
  have he : (∫ t : ℝ in Ici 0, (((1+t)*Real.exp (-(2*t)):ℝ):ℂ)*((r:ℂ)*ψ (r,0))) =
      (3/4:ℂ)*(r:ℂ)*ψ (r,0) := by
    rw [integral_mul_const,integral_complex_ofReal,integral_Ici_eq_integral_Ioi,tripleBoundary_axis_mass]
    push_cast
    ring
  have hsub : (∫ t : ℝ in Ici 0, (((1+t)*Real.exp (-(2*t)):ℝ):ℂ)*
      (ψ (r,t/b)*(r+t/(2*b):ℝ)-ψ (r,0)*(r:ℝ))) =
      tripleQuadrantAxisScaled ψ b r-(3/4:ℂ)*(r:ℂ)*ψ (r,0) := by
    rw [← he]
    unfold tripleQuadrantAxisScaled
    convert integral_sub hi hj using 1
    congr 1
    ext t
    simp [mul_sub, mul_comm]
    <;> ring
  rw [← hsub,integral_Ici_eq_integral_Ioi]
  exact tripleBoundary_axis_trace_integral ψ hψ M N b r hM hN hb hr hbound hD

end
end HigherCorrelations
