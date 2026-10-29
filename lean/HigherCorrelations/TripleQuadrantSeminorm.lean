import HigherCorrelations.TripleQuadrantSeminormDefinitions
import HigherCorrelations.TripleQuadrantGeometry
import Mathlib.Analysis.Normed.Group.Bounded

/-! UNCONDITIONAL control by the manuscript's sum of three quadrant suprema. -/
namespace HigherCorrelations
noncomputable section
open Set

theorem tripleQuadrantSup_bounds (f : ℝ × ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    0 ≤ tripleQuadrantSup f ∧ ∀ p ∈ tripleQuadrant, ‖f p‖ ≤ tripleQuadrantSup f := by
  have hb : BddAbove ((fun p => ‖f p‖) '' tripleQuadrant) :=
    (hf.norm.bddAbove_range_of_hasCompactSupport hc.norm).mono (image_subset_range _ _)
  have hh : ∀ p ∈ tripleQuadrant, ‖f p‖ ≤ tripleQuadrantSup f :=
    fun p hp => le_csSup hb (mem_image_of_mem _ hp)
  exact ⟨(norm_nonneg _).trans (hh (0,0) ⟨le_rfl,le_rfl⟩),hh⟩

theorem tripleQuadrant_derivative_coordinate_bound (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (D₁ D₂ : ℝ) (h₁ : ‖fderiv ℝ f p (1,0)‖ ≤ D₁)
    (h₂ : ‖fderiv ℝ f p (0,1)‖ ≤ D₂) : ‖fderiv ℝ f p‖ ≤ D₁+D₂ := by
  have hD₁ := (norm_nonneg _).trans h₁
  have hD₂ := (norm_nonneg _).trans h₂
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hD₁ hD₂)
  intro v
  have hv : v = v.1 • ((1,0):ℝ × ℝ)+v.2 • ((0,1):ℝ × ℝ) := by ext <;> simp
  calc
    ‖fderiv ℝ f p v‖ = ‖v.1 • fderiv ℝ f p (1,0)+v.2 • fderiv ℝ f p (0,1)‖ := by
      conv_lhs => rw [hv]
      simp only [map_add,map_smul]
    _ ≤ ‖v.1‖*‖fderiv ℝ f p (1,0)‖+‖v.2‖*‖fderiv ℝ f p (0,1)‖ := by
      simpa only [norm_smul] using norm_add_le (v.1 • fderiv ℝ f p (1,0)) (v.2 • fderiv ℝ f p (0,1))
    _ ≤ ‖v‖*D₁+‖v‖*D₂ := add_le_add
      (mul_le_mul (norm_fst_le v) h₁ (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (norm_snd_le v) h₂ (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem tripleQuadrantN1_bounds (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    0 ≤ tripleQuadrantN1 ψ ∧
    (∀ p ∈ tripleQuadrant, ‖ψ p‖ ≤ tripleQuadrantN1 ψ) ∧
    (∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖ ≤ tripleQuadrantN1 ψ) := by
  have hd : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have h₀ := tripleQuadrantSup_bounds ψ hψ.continuous hc
  have h₁ := tripleQuadrantSup_bounds (fun p => fderiv ℝ ψ p (1,0))
    (hd.clm_apply continuous_const) (hc.fderiv_apply ℝ (1,0))
  have h₂ := tripleQuadrantSup_bounds (fun p => fderiv ℝ ψ p (0,1))
    (hd.clm_apply continuous_const) (hc.fderiv_apply ℝ (0,1))
  refine ⟨by unfold tripleQuadrantN1; exact add_nonneg (add_nonneg h₀.1 h₁.1) h₂.1,?_,?_⟩
  · intro p hp
    have hh := h₀.2 p hp
    unfold tripleQuadrantN1
    linarith [h₁.1,h₂.1]
  · intro p hp
    have hh := tripleQuadrant_derivative_coordinate_bound ψ p _ _ (h₁.2 p hp) (h₂.2 p hp)
    unfold tripleQuadrantN1
    linarith [h₀.1]

end
end HigherCorrelations
