import HigherCorrelations.TripleBoundaryMajorant
import HigherCorrelations.TripleBoundaryHeight
import HigherCorrelations.TripleQuadrantIdentity

/-! UNCONDITIONAL integration of the exact residual, through a continuous
majorant. No measurability of separately split arithmetic errors is assumed. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

set_option maxHeartbeats 800000 in
theorem tripleBoundaryMajorant_integral (A H D W V T κ : ℝ)
    (hA : 0≤A) (hH : 0≤H) (hD : 0≤D) (hW : 0≤W) (hV : 0≤V)
    (hT : 2*Real.pi<T) :
    (∫ p in tripleBoundaryBox, tripleBoundaryMajorant A H D W V T κ p) ≤
      A*V*(Real.log (2*T+2)^2/(4*Real.log (tripleTestBase T)^2)+
        Real.log (2*T+2)^3/T+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^4) +
      H*(1+W)*(2*Real.log (2*T+2)/Real.log (tripleTestBase T)+
        Real.log (2*T+2)^2/Real.log (tripleTestBase T)^2) +
      (2*D*Real.log (2*T+2)/Real.log (tripleTestBase T)+8/T+
        55296*tripleResonanceDecayConstant/Real.log (tripleTestBase T)^2) := by
  let L := Real.log (2*T+2)
  let b := Real.log (tripleTestBase T)
  let c := D*L+4*b/T
  let R := tripleResonanceDecayConstant
  let d := L^3/T+(tripleTestBase T)^(-κ)*L^4
  let f1 : ℝ × ℝ → ℝ := fun p => A*V*(L^2*(Real.exp (-((2*b)*p.1))*Real.exp (-((2*b)*p.2)))+d)
  let f2 : ℝ × ℝ → ℝ := fun p => H*(1+W)*(L*(Real.exp (-(b*p.1))+Real.exp (-(b*p.2)))+
    L^2*(Real.exp (-(b*p.1))*Real.exp (-(b*p.2))))
  let f3 : ℝ × ℝ → ℝ := fun p => c*(Real.exp (-(b*p.1))+Real.exp (-(b*p.2)))
  let f4 : ℝ × ℝ → ℝ := fun p => 3456*R*(Real.exp (-((b/4)*p.1))*Real.exp (-((b/4)*p.2)))
  have ht := tripleTestBase_bounds T hT
  have hT0 : 0<T := by linarith [ht.1]
  have hb : 0<b := Real.log_pos ht.2.1
  have hL : 0≤L := le_trans (by norm_num) (tripleBudget_height_log T ht.1)
  have hR : 0≤R := tripleResonanceDecayConstant_pos.le
  have hc : 0≤c := by dsimp [c]; positivity
  have hi1 : IntegrableOn f1 tripleBoundaryBox :=
    (by dsimp [f1]; fun_prop : Continuous f1).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hi2 : IntegrableOn f2 tripleBoundaryBox :=
    (by dsimp [f2]; fun_prop : Continuous f2).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hi3 : IntegrableOn f3 tripleBoundaryBox :=
    (by dsimp [f3]; fun_prop : Continuous f3).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hi4 : IntegrableOn f4 tripleBoundaryBox :=
    (by dsimp [f4]; fun_prop : Continuous f4).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hi12 : IntegrableOn (fun p => f1 p+f2 p) tripleBoundaryBox := hi1.add hi2
  have hi123 : IntegrableOn (fun p => f1 p+f2 p+f3 p) tripleBoundaryBox := hi12.add hi3
  change (∫ p in tripleBoundaryBox, f1 p+f2 p+f3 p+f4 p) ≤ _
  rw [integral_add hi123 hi4,integral_add hi12 hi3,integral_add hi1 hi2]
  dsimp only [f1,f2,f3,f4]
  simp_rw [integral_const_mul]
  have h1 := mul_le_mul_of_nonneg_left (tripleBoundary_box_origin_constant L b d hb) (mul_nonneg hA hV)
  have h2 := mul_le_mul_of_nonneg_left (tripleBoundary_box_envelope L b hL hb) (show 0≤H*(1+W) by positivity)
  have h3 := mul_le_mul_of_nonneg_left (tripleBoundary_box_axis_sum b hb) hc
  have h4 := mul_le_mul_of_nonneg_left (tripleBoundary_origin_box (b/4) (by positivity)) (show 0≤3456*R by positivity)
  apply (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq
  change A*V*(L^2/(4*b^2)+d)+H*(1+W)*(2*L/b+L^2/b^2)+c*(2/b)+3456*R*(1/(b/4)^2) =
    A*V*(L^2/(4*b^2)+L^3/T+(tripleTestBase T)^(-κ)*L^4)+
      H*(1+W)*(2*L/b+L^2/b^2)+(2*D*L/b+8/T+55296*R/b^2)
  dsimp only [c,d]
  field_simp [hb.ne',hT0.ne']
  <;> ring

set_option maxHeartbeats 800000 in
theorem tripleBoundary_integrated_envelope : ∃ A : ℝ, 0<A ∧ ∃ H : ℝ, 0<H ∧ ∃ D : ℝ, 0<D ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T κ M : ℝ,
    0≤W → (∀ u, ω u≤W) → 2*Real.pi<T → 0<κ → 0≤M →
    ∀ (ψ : ℝ × ℝ → ℂ), (∀ p ∈ tripleQuadrant, ‖ψ p‖≤M) →
    (∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ) →
    (∫ p : ℝ × ℝ, ‖tripleQuadrantAmplitude ψ p*
      tripleQuadrantRemainder ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)‖) ≤
    M*(A*(1+fourierDerivativeL1 ω 1)*(Real.log (2*T+2)^2/(4*Real.log (tripleTestBase T)^2)+
      Real.log (2*T+2)^3/T+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^4) +
    H*(1+W)*(2*Real.log (2*T+2)/Real.log (tripleTestBase T)+
      Real.log (2*T+2)^2/Real.log (tripleTestBase T)^2) +
    (2*D*Real.log (2*T+2)/Real.log (tripleTestBase T)+8/T+
      55296*tripleResonanceDecayConstant/Real.log (tripleTestBase T)^2)) := by
  obtain ⟨A,hA,H,hH,D,hD,h⟩ := tripleBoundary_majorization
  refine ⟨A,hA,H,hH,D,hD,?_⟩
  intro ω hω W T κ M hW hωW hT hκ hM ψ hψ hs
  have hV : 0≤1+fourierDerivativeL1 ω 1 := by linarith [fourierDerivativeL1_nonneg ω 1]
  simp only [norm_mul]
  have hh := tripleBoundary_supported_integral ψ
    (fun p => ‖tripleQuadrantRemainder ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)‖)
    (tripleBoundaryMajorant A H D W (1+fourierDerivativeL1 ω 1) T κ) M κ hM hκ.le hψ hs
    (fun _ => norm_nonneg _) (tripleBoundaryMajorant_continuous _ _ _ _ _ _ _)
    (fun p _ => tripleBoundaryMajorant_nonneg _ _ _ _ _ _ _ hA.le hH.le hD.le hW hV hT p)
    (h ω hω W T κ hW hωW hT hκ)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (tripleBoundaryMajorant_integral _ _ _ _ _ _ _ hA.le hH.le hD.le hW hV hT) hM)

end
end HigherCorrelations
