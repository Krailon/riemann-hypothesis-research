import HigherCorrelations.TripleQuadrantWeightedBound
import HigherCorrelations.TripleQuadrantTraceBounds
import HigherCorrelations.TripleQuadrantSeminorm
import HigherCorrelations.TripleBoundaryHeight

/-! UNCONDITIONAL leading-term comparison with the complete quadrant functional.
The two logarithmic scales and both axis traces are explicit. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

set_option maxHeartbeats 800000 in
theorem tripleQuadrant_main_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ (ψ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∀ T κ : ℝ, 2*Real.pi*Real.exp 1 ≤ T → 0 ≤ κ →
    (∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-κ) →
    ‖(∫ p in tripleQuadrant,
        ψ p*(tripleRetainedMain ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2):ℂ)) /
      (Real.log T:ℂ)-tripleQuadrantLimit ψ‖ ≤
      C*tripleQuadrantN1 ψ/Real.log (tripleTestBase T) := by
  let c := Real.log (2*Real.pi)
  let d := Real.log 2
  have hc : 0 ≤ c := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hd : 0 ≤ d := Real.log_nonneg (by norm_num)
  refine ⟨((1+c)^2+c*(2+c)+6*(1+d)+6*d)/4,by positivity,?_⟩
  intro ω hω ψ hψ hcomp T κ hT hκ hs
  let b := Real.log (tripleTestBase T)
  let S := tripleQuadrantN1 ψ
  have ht := tripleBoundary_height T hT
  have hb : 1 ≤ b := ht.2.1
  have hb0 : 0 < b := by linarith
  have hq : Real.log T=b+c := ht.2.2.1
  have hq0 : 0 < Real.log T := by rw [hq]; positivity
  have hB : 0 < tripleTestBase T := lt_trans zero_lt_one (tripleTestBase_bounds T ht.1).2.1
  obtain ⟨hS,hbound,hD⟩ := tripleQuadrantN1_bounds ψ hψ hcomp
  have hμ := tripleSmoothingMean_bounds ω hω
  let o := (b:ℂ)^2*tripleQuadrantOriginLead ψ b
  let o₀ := ψ (0,0)/4
  let a := tripleQuadrantAxisLead ψ b
  let a' := tripleQuadrantAxisLead (fun p => ψ p.swap) b
  let a₀ := (3/4:ℂ)*(∫ r : ℝ in Ici 0, (r:ℂ)*ψ (r,0))
  let a₀' := (3/4:ℂ)*(∫ r : ℝ in Ici 0, (r:ℂ)*ψ (0,r))
  have ho : ‖o-o₀‖ ≤ S/(4*b) := tripleQuadrantOrigin_scaled_approximation ψ hψ S S b hS hb0 hbound hD
  have ho₀ : ‖o₀‖ ≤ S/4 := by
    dsimp [o₀]
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right (hbound (0,0) ⟨le_rfl,le_rfl⟩) (by norm_num)
  have ha : ‖a-a₀‖ ≤ S/(2*b)+S/(4*b) :=
    tripleQuadrant_axis_integrated_approximation ψ hψ hcomp S S b κ hS hS hb0 hκ hbound hD hs
  have ha' : ‖a'-a₀'‖ ≤ S/(2*b)+S/(4*b) := by
    exact tripleQuadrant_axis_integrated_approximation (fun p => ψ p.swap)
      (tripleQuadrant_swap_smooth ψ hψ) (tripleQuadrant_swap_compact ψ hcomp)
      S S b κ hS hS hb0 hκ (fun p hp => hbound p.swap ⟨hp.2,hp.1⟩)
      (tripleQuadrant_swap_derivative ψ hψ S hD)
      (fun p hp hn => by simpa [add_comm] using hs p.swap ⟨hp.2,hp.1⟩ hn)
  have hz : ‖(a+a')-(a₀+a₀')‖ ≤ 3*S/(2*b) := by
    calc
      _ = ‖(a-a₀)+(a'-a₀')‖ := by congr 1; ring
      _ ≤ ‖a-a₀‖+‖a'-a₀'‖ := norm_add_le _ _
      _ ≤ (S/(2*b)+S/(4*b))+(S/(2*b)+S/(4*b)) := add_le_add ha ha'
      _ = _ := by ring
  have ha₀ : ‖a₀‖ ≤ (3/4)*S := by
    dsimp [a₀]
    rw [norm_mul]
    norm_num only [norm_div,Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (tripleQuadrant_axis_trace_bound ψ S κ hS hκ hbound hs) (by norm_num)
  have ha₀' : ‖a₀'‖ ≤ (3/4)*S := by
    dsimp [a₀']
    rw [norm_mul]
    norm_num only [norm_div,Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (tripleQuadrant_axis_trace_bound (fun p => ψ p.swap) S κ hS hκ
      (fun p hp => hbound p.swap ⟨hp.2,hp.1⟩)
      (fun p hp hn => by simpa [add_comm] using hs p.swap ⟨hp.2,hp.1⟩ hn)) (by norm_num)
  have hz₀ : ‖a₀+a₀'‖ ≤ 3*S/2 :=
    (norm_add_le _ _).trans ((add_le_add ha₀ ha₀').trans_eq (by ring))
  have hh := tripleQuadrant_weighted_bound S b c d (tripleSmoothingMean ω) hS hb hc hμ.1 hμ.2
    o o₀ (a+a') (a₀+a₀') ho ho₀ hz hz₀
  have he : (∫ p in tripleQuadrant,
        ψ p*(tripleRetainedMain ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2):ℂ)) /
      (Real.log T:ℂ) = (((b+c)^2/b^2:ℝ):ℂ)*o+
        ((1+tripleSmoothingMean ω/(b+c):ℝ):ℂ)*(a+a') := by
    rw [tripleQuadrant_main_integral ω T _ hB ψ hψ.continuous hcomp,hq]
    dsimp [o,a,a',b]
    have hbC : (Real.log (tripleTestBase T):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb0.ne'
    have hqC : ((Real.log (tripleTestBase T)+c:ℝ):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by rw [← hq]; exact hq0.ne')
    push_cast at hqC ⊢
    field_simp [hbC,hqC]
    <;> ring
  rw [he,tripleQuadrant_limit_split ψ hψ.continuous κ hκ hs]
  convert hh using 1 <;> dsimp [o₀,a₀,a₀',S,b] <;> congr 1 <;> ring

end
end HigherCorrelations
