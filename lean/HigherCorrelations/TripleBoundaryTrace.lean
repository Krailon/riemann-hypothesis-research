import HigherCorrelations.TripleBoundaryIntegration
import Mathlib.Analysis.Calculus.MeanValue

/-! UNCONDITIONAL quantitative trace estimates. N is an explicit derivative
majorant on the quadrant; these statements do not infer smoothness of the
zero extension or integrate an unproved local asymptotic. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrant_convex : Convex ℝ tripleQuadrant :=
  (convex_Ici (0:ℝ)).prod (convex_Ici (0:ℝ))

theorem tripleBoundary_trace_lipschitz (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (N : ℝ)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖≤N)
    (p q : ℝ × ℝ) (hp : p ∈ tripleQuadrant) (hq : q ∈ tripleQuadrant) :
    ‖ψ p-ψ q‖≤N*‖p-q‖ :=
  tripleQuadrant_convex.norm_image_sub_le_of_norm_fderiv_le
    (fun _ _ => hψ.differentiable (by norm_num) |>.differentiableAt) hD hq hp

theorem tripleBoundary_origin_trace (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (N b : ℝ) (hN : 0≤N) (hb : 0<b)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖≤N)
    (u v : ℝ) (hu : 0≤u) (hv : 0≤v) :
    ‖ψ (u/b,v/b)-ψ (0,0)‖≤N*(u+v)/b := by
  have h := tripleBoundary_trace_lipschitz ψ hψ N hD (u/b,v/b) (0,0)
    ⟨by positivity,by positivity⟩ ⟨le_rfl,le_rfl⟩
  have hn : ‖((u/b,v/b):ℝ × ℝ)-(0,0)‖ ≤ (u+v)/b := by
    simp only [Prod.mk_sub_mk,sub_zero,Prod.norm_def,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hu hb.le),abs_of_nonneg (div_nonneg hv hb.le)]
    exact max_le (by apply div_le_div_of_nonneg_right _ hb.le; linarith)
      (by apply div_le_div_of_nonneg_right _ hb.le; linarith)
  exact h.trans (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hn hN)

theorem tripleBoundary_axis_trace (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (N b : ℝ) (hb : 0<b)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖≤N)
    (r t : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ t) :
    ‖ψ (r,t/b)-ψ (r,0)‖≤N*t/b := by
  have h := tripleBoundary_trace_lipschitz ψ hψ N hD (r,t/b) (r,0)
    ⟨hr,by positivity⟩ ⟨hr,le_rfl⟩
  simpa [Prod.norm_def,abs_of_nonneg hs,abs_of_pos hb,max_eq_right (div_nonneg hs hb.le),mul_div_assoc] using h

theorem tripleBoundary_origin_kernel_integrable :
    IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(2*(p.1+p.2)))) tripleQuadrant := by
  have h := tripleBoundary_product_moment_integrable 0 0 2 2 (by norm_num) (by norm_num)
  convert h using 1
  ext p
  simp only [pow_zero,one_mul,← Real.exp_add]
  congr 1
  ring

theorem tripleBoundary_origin_first_integrable :
    IntegrableOn (fun p : ℝ × ℝ => (p.1+p.2)*Real.exp (-(2*(p.1+p.2)))) tripleQuadrant := by
  have h := (tripleBoundary_product_moment_integrable 1 0 2 2 (by norm_num) (by norm_num)).add
    (tripleBoundary_product_moment_integrable 0 1 2 2 (by norm_num) (by norm_num))
  convert h using 1
  ext p
  simp only [Pi.add_apply]
  rw [show -(2*(p.1+p.2))= -(2*p.1)+ -(2*p.2) by ring,Real.exp_add]
  ring

theorem tripleBoundary_origin_trace_integral (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (N b : ℝ) (hN : 0≤N) (hb : 0<b)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖≤N) :
    ‖∫ p : ℝ × ℝ in tripleQuadrant,
      (Real.exp (-(2*(p.1+p.2))):ℂ)*(ψ (p.1/b,p.2/b)-ψ (0,0))‖ ≤ N/(4*b) := by
  have hi := tripleBoundary_origin_first_integrable.const_mul (N/b)
  have hbound : ∀ᵐ p : ℝ × ℝ ∂volume.restrict tripleQuadrant,
      ‖(Real.exp (-(2*(p.1+p.2))):ℂ)*(ψ (p.1/b,p.2/b)-ψ (0,0))‖ ≤
      (N/b)*((p.1+p.2)*Real.exp (-(2*(p.1+p.2)))) := by
    filter_upwards [self_mem_ae_restrict tripleQuadrant_measurable] with p hp
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_left
      (tripleBoundary_origin_trace ψ hψ N b hN hb hD p.1 p.2 hp.1 hp.2) (Real.exp_pos (-(2*(p.1+p.2)))).le
    convert h using 1 <;> ring
  have h := norm_integral_le_of_norm_le hi hbound
  rw [integral_const_mul,tripleBoundary_origin_first_moment] at h
  convert h using 1 <;> ring

theorem tripleBoundary_axis_trace_integral (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (M N b r : ℝ)
    (hM : 0≤M) (hN : 0≤N) (hb : 0<b) (hr : 0 ≤ r)
    (hbound : ∀ p ∈ tripleQuadrant, ‖ψ p‖≤M)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖≤N) :
    ‖∫ t : ℝ in Ioi 0, (((1+t)*Real.exp (-(2*t)):ℝ):ℂ)*
      (ψ (r,t/b)*(r+t/(2*b):ℝ)-ψ (r,0)*(r:ℝ))‖ ≤ N*r/(2*b)+M/(4*b) := by
  have hi : IntegrableOn (fun t : ℝ => t*(1+t)*Real.exp (-(2*t))) (Ioi 0) := by
    have hh := (tripleBoundary_moment_integrable 1 2 (by norm_num)).add
      (tripleBoundary_moment_integrable 2 2 (by norm_num))
    convert hh using 1
    ext t
    simp only [Pi.add_apply]
    ring
  have hpt : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ‖(((1+t)*Real.exp (-(2*t)):ℝ):ℂ)*
        (ψ (r,t/b)*(r+t/(2*b):ℝ)-ψ (r,0)*(r:ℝ))‖ ≤
      (N*r/b+M/(2*b))*(t*(1+t)*Real.exp (-(2*t))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0≤t := le_of_lt ht
    have hψt := hbound (r,t/b) ⟨hr,div_nonneg ht0 hb.le⟩
    have hd := tripleBoundary_axis_trace ψ hψ N b hb hD r t hr ht0
    have he : ψ (r,t/b)*(r+t/(2*b):ℝ)-ψ (r,0)*(r:ℝ) =
        (ψ (r,t/b)-ψ (r,0))*(r:ℝ)+ψ (r,t/b)*(t/(2*b):ℝ) := by push_cast; ring
    have hh : ‖ψ (r,t/b)*(r+t/(2*b):ℝ)-ψ (r,0)*(r:ℝ)‖ ≤
        (N*t/b)*r+M*(t/(2*b)) := by
      rw [he]
      apply (norm_add_le _ _).trans
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,
        abs_of_nonneg (div_nonneg ht0 (by positivity : 0≤2*b))]
      exact add_le_add (mul_le_mul_of_nonneg_right hd hr)
        (mul_le_mul_of_nonneg_right hψt (by positivity))
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(1+t)*Real.exp (-(2*t)))]
    have hz := mul_le_mul_of_nonneg_left hh
      (by positivity : 0≤(1+t)*Real.exp (-(2*t)))
    convert hz using 1 <;> ring
  have hh := norm_integral_le_of_norm_le (hi.const_mul (N*r/b+M/(2*b))) hpt
  rw [integral_const_mul,tripleBoundary_axis_first_moment] at hh
  convert hh using 1 <;> ring

end
end HigherCorrelations
