import HigherCorrelations.TripleBoundaryNamed
import HigherCorrelations.TripleBoundaryScales
import HigherCorrelations.TripleBoundaryBox

/-! UNCONDITIONAL integrated bound for all eight non-H errors, with the
origin Jacobian and the support-margin decay separately visible. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

set_option maxHeartbeats 800000 in
theorem tripleBoundary_named_integral : ∃ A : ℝ, 0<A ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ T κ M : ℝ,
    2*Real.pi<T → 0<κ → 0≤M → ∀ (ψ : ℝ × ℝ → ℂ),
    (∀ p ∈ tripleQuadrant, ‖ψ p‖≤M) →
    (∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ) →
    (∫ p : ℝ × ℝ, ‖tripleQuadrantAmplitude ψ p‖*
      (∑ e : TripleBudgetError,
        ‖tripleBudgetError ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) e‖)) ≤
    M*A*(1+fourierDerivativeL1 ω 1)*
      (Real.log (2*T+2)^2/(4*Real.log (tripleTestBase T)^2)+Real.log (2*T+2)^3/T+
        (tripleTestBase T)^(-κ)*Real.log (2*T+2)^4) := by
  obtain ⟨A,hA,ha⟩ := tripleBoundary_named_bound
  refine ⟨A,hA,?_⟩
  intro ω hω T κ M hT hκ hM ψ hψ hs
  let L := Real.log (2*T+2)
  let b := Real.log (tripleTestBase T)
  let V := 1+fourierDerivativeL1 ω 1
  let d := L^3/T+(tripleTestBase T)^(-κ)*L^4
  let E : ℝ × ℝ → ℝ := fun p => A*V*
    (L^2*(Real.exp (-((2*b)*p.1))*Real.exp (-((2*b)*p.2)))+d)
  have ht := tripleTestBase_bounds T hT
  have hT0 : 0<T := by linarith [ht.1]
  have hbase : 0<tripleTestBase T := by linarith [ht.2.1]
  have hb : 0<b := Real.log_pos ht.2.1
  have hL : 0≤L := le_trans (by norm_num) (tripleBudget_height_log T ht.1)
  have hV : 0≤V := by dsimp [V]; linarith [fourierDerivativeL1_nonneg ω 1]
  have hd : 0≤d := by dsimp [d]; positivity
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hpoint (p : ℝ × ℝ) (hp : p ∈ tripleQuadrantMargin κ) :
      (∑ e : TripleBudgetError,
        ‖tripleBudgetError ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) e‖) ≤ E p := by
    obtain ⟨hx,hy,hz⟩ := tripleQuadrant_scale_range κ T p hT hp
    obtain ⟨hzt,hzratio⟩ := tripleBoundary_product_height κ T hκ.le hT p hp
    have hh := ha ω hω T _ _ ht.1 hx hy hzt
    apply hh.trans
    have he : L^2/((tripleTestBase T)^p.1*(tripleTestBase T)^p.2)^2 =
        L^2*(Real.exp (-((2*b)*p.1))*Real.exp (-((2*b)*p.2))) := by
      rw [div_eq_mul_one_div,tripleBoundary_inverse_product_square _ _ _ hbase]
    change A*V*(L^2/((tripleTestBase T)^p.1*(tripleTestBase T)^p.2)^2+L^3/T+
      ((tripleTestBase T)^p.1*(tripleTestBase T)^p.2)/T*L^4) ≤ _
    rw [he]
    dsimp only [E,d]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA.le hV)
    have hh := mul_le_mul_of_nonneg_right hzratio (pow_nonneg hL 4)
    linarith only [hh]
  have hh := tripleBoundary_supported_integral ψ
    (fun p => ∑ e : TripleBudgetError,
      ‖tripleBudgetError ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) e‖)
    E M κ hM hκ.le hψ hs (fun _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    hE (fun p _ => by dsimp [E]; positivity) hpoint
  dsimp only [E] at hh
  rw [integral_const_mul] at hh
  have hbnd := mul_le_mul_of_nonneg_left (tripleBoundary_box_origin_constant L b d hb)
    (show 0≤M*(A*V) by positivity)
  apply hh.trans
  convert hbnd using 1 <;> dsimp [L,b,V,d] <;> ring

end
end HigherCorrelations
