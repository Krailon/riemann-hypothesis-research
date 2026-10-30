import HigherCorrelations.SignedTestRegularity
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! UNCONDITIONAL global C1 control of all six quadrant tests. -/
namespace HigherCorrelations
noncomputable section
open Set

theorem signedSup_bounds (f : ℝ × ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    0 ≤ signedSup f ∧ ∀ p, ‖f p‖ ≤ signedSup f := by
  have hb := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hh : ∀ p, ‖f p‖ ≤ signedSup f := fun p => le_csSup hb (mem_range_self p)
  exact ⟨(norm_nonneg _).trans (hh (0,0)),hh⟩

theorem signedPullback_fderiv_norm (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (j : Fin 6) (p v : ℝ × ℝ) :
    ‖fderiv ℝ (signedPullback φ j) p v‖ = ‖fderiv ℝ φ (signedSector j p) (signedSector j v)‖ := by
  have he : fderiv ℝ (φ ∘ signedSectorEquiv j) p =
      (fderiv ℝ φ (signedSector j p)).comp (signedSectorEquiv j).toContinuousLinearMap := by
    exact ((hφ.differentiable (by simp) (signedSector j p)).hasFDerivAt.comp p
      (signedSectorEquiv j).hasFDerivAt).fderiv
  unfold signedPullback signedConjugate
  split_ifs
  · change ‖fderiv ℝ (φ ∘ signedSectorEquiv j) p v‖ = _
    rw [he]
    rfl
  · rw [fderiv_star]
    change ‖star (fderiv ℝ (φ ∘ signedSectorEquiv j) p v)‖ = _
    rw [norm_star,he]
    rfl

theorem signedSector_coordinate_norm (j : Fin 6) :
    ‖signedSector j (1,0)‖ ≤ 1 ∧ ‖signedSector j (0,1)‖ ≤ 1 := by
  fin_cases j <;> norm_num [signedSector,Prod.norm_def]

theorem signedPullback_N1_bound (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (j : Fin 6) : tripleQuadrantN1 (signedPullback φ j) ≤ 2*signedC1 φ := by
  have hd := hφ.continuous_fderiv (by simp)
  have h0 := signedSup_bounds φ hφ.continuous hc
  have h1 := signedSup_bounds (fun p => fderiv ℝ φ p (1,0))
    (hd.clm_apply continuous_const) (hc.fderiv_apply ℝ (1,0))
  have h2 := signedSup_bounds (fun p => fderiv ℝ φ p (0,1))
    (hd.clm_apply continuous_const) (hc.fderiv_apply ℝ (0,1))
  have hb (v : ℝ × ℝ) (hv : ‖signedSector j v‖ ≤ 1) (p : ℝ × ℝ) :
      ‖fderiv ℝ (signedPullback φ j) p v‖ ≤
        signedSup (fun p => fderiv ℝ φ p (1,0))+signedSup (fun p => fderiv ℝ φ p (0,1)) := by
    rw [signedPullback_fderiv_norm φ hφ j p v]
    have hh := tripleQuadrant_derivative_coordinate_bound φ (signedSector j p) _ _
      (h1.2 _) (h2.2 _)
    exact ((fderiv ℝ φ (signedSector j p)).le_opNorm _).trans
      (by simpa only [mul_one] using mul_le_mul hh hv (norm_nonneg _) (add_nonneg h1.1 h2.1))
  have sup_le (f : ℝ × ℝ → ℂ) (D : ℝ) (hf : ∀ p, ‖f p‖ ≤ D) : tripleQuadrantSup f ≤ D :=
    csSup_le (by exact ⟨‖f (0,0)‖,mem_image_of_mem _ ⟨le_rfl,le_rfl⟩⟩)
      (by rintro _ ⟨p,hp,rfl⟩; exact hf p)
  have hs0 := sup_le (signedPullback φ j) _ (fun p => by
    rw [signedPullback,signedConjugate_norm]; exact h0.2 _)
  have hs1 := sup_le _ _ (hb (1,0) (signedSector_coordinate_norm j).1)
  have hs2 := sup_le _ _ (hb (0,1) (signedSector_coordinate_norm j).2)
  unfold tripleQuadrantN1 signedC1
  linarith [h0.1]

end
end HigherCorrelations
