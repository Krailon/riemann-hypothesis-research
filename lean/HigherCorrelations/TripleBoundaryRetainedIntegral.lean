import HigherCorrelations.TripleBoundaryRetainedBounds

/-! UNCONDITIONAL integrated retained evaluation error, with the diagonal,
smoothing, and resonance losses displayed separately. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

set_option maxHeartbeats 800000 in
theorem tripleBoundary_retained_integral : ∃ D : ℝ, 0<D ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ T κ M : ℝ,
    2*Real.pi<T → 0<κ → 0≤M → ∀ (ψ : ℝ × ℝ → ℂ),
    (∀ p ∈ tripleQuadrant, ‖ψ p‖≤M) →
    (∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ) →
    (∫ p : ℝ × ℝ, ‖tripleQuadrantAmplitude ψ p‖*
      ‖tripleBudgetRetained ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)-
        (tripleRetainedMain ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2):ℂ)‖) ≤
    M*(2*D*Real.log (2*T+2)/Real.log (tripleTestBase T)+8/T+
      55296*tripleResonanceDecayConstant/Real.log (tripleTestBase T)^2) := by
  obtain ⟨D,hD,hd⟩ := tripleRetainedErrorD_uniform
  refine ⟨D,hD,?_⟩
  intro ω hω T κ M hT hκ hM ψ hψ hs
  let B := tripleTestBase T
  let L := Real.log (2*T+2)
  let b := Real.log B
  let c := D*L+4*b/T
  let R := tripleResonanceDecayConstant
  let E : ℝ × ℝ → ℝ := fun p => c*(Real.exp (-(b*p.1))+Real.exp (-(b*p.2)))+
    3456*R*(Real.exp (-((b/4)*p.1))*Real.exp (-((b/4)*p.2)))
  have ht := tripleTestBase_bounds T hT
  have hT0 : 0<T := by linarith [ht.1]
  have hB : 0<B := by dsimp [B]; linarith [ht.2.1]
  have hb : 0<b := Real.log_pos ht.2.1
  have hL : 0≤L := le_trans (by norm_num) (tripleBudget_height_log T ht.1)
  have hR : 0≤R := tripleResonanceDecayConstant_pos.le
  have hc : 0≤c := by dsimp [c]; positivity
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hpbound (p : ℝ × ℝ) (hp : p ∈ tripleQuadrantMargin κ) :
      ‖tripleBudgetRetained ω T (B^p.1) (B^p.2)-(tripleRetainedMain ω T (B^p.1) (B^p.2):ℂ)‖≤E p := by
    obtain ⟨hx,hy,hz⟩ := tripleQuadrant_scale_range κ T p hT hp
    have hbox := tripleQuadrantMargin_subset_box κ hκ.le hp
    have hz1 : 1≤B^p.1*B^p.2 := one_le_mul_of_one_le_of_one_le hx hy
    have hmain := tripleRetained_combined_bound D ω hω T (B^p.1) (B^p.2) ht.1 hx hy
      (hd ω T (B^p.1) (B^p.2) hω ht.1 hx hy)
    have hdiag := tripleBoundary_diagonal_scale (B^p.1) (B^p.2) hx hy
    have hg := tripleBoundary_G_frequency B ht.2.1 p hbox
    have hr := tripleBoundary_resonance_scale (B^p.1*B^p.2) hz1
    have he : (B^p.1*B^p.2)^(-(1/4:ℝ)) =
        Real.exp (-((b/4)*p.1))*Real.exp (-((b/4)*p.2)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg hB.le _),
        ← Real.rpow_mul hB.le,← Real.rpow_mul hB.le]
      simp only [Real.rpow_def_of_pos hB]
      congr 2 <;> dsimp [b] <;> congr 1 <;> ring
    have hh := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hdiag (show 0≤D*L by positivity))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2)) hT0.le))
      (mul_le_mul_of_nonneg_left hr hR)
    apply hmain.trans
    apply hh.trans_eq
    rw [he,tripleBoundary_inverse_scale B p.1 hB,tripleBoundary_inverse_scale B p.2 hB]
    dsimp [E,c,b,R,L]
    ring
  have hh := tripleBoundary_supported_integral ψ
    (fun p => ‖tripleBudgetRetained ω T (B^p.1) (B^p.2)-
      (tripleRetainedMain ω T (B^p.1) (B^p.2):ℂ)‖) E M κ hM hκ.le hψ hs
    (fun _ => norm_nonneg _) hE (fun p _ => by dsimp [E]; positivity) hpbound
  have hi1 : IntegrableOn (fun p : ℝ × ℝ => c*(Real.exp (-(b*p.1))+Real.exp (-(b*p.2)))) tripleBoundaryBox :=
    (by fun_prop : Continuous _).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hi2 : IntegrableOn (fun p : ℝ × ℝ => 3456*R*(Real.exp (-((b/4)*p.1))*Real.exp (-((b/4)*p.2)))) tripleBoundaryBox :=
    (by fun_prop : Continuous _).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  dsimp only [E] at hh
  rw [integral_add hi1 hi2,integral_const_mul,integral_const_mul] at hh
  have hh1 := mul_le_mul_of_nonneg_left (tripleBoundary_box_axis_sum b hb) hc
  have hh2 := mul_le_mul_of_nonneg_left (tripleBoundary_origin_box (b/4) (by positivity))
    (show 0≤3456*R by positivity)
  apply hh.trans
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hh1 hh2) hM
  have he : M*(c*(2/b)+3456*R*(1/(b/4)^2)) =
      M*(2*D*L/b+8/T+55296*R/b^2) := by
    dsimp only [c]
    field_simp [hb.ne',hT0.ne']
    <;> ring
  rw [he] at hsum
  exact hsum

end
end HigherCorrelations
