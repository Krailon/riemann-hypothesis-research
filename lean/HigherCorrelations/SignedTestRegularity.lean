import HigherCorrelations.SignedTestDefinitions
import HigherCorrelations.SignedSectorGeometry
import HigherCorrelations.TripleQuadrantSeminorm
import HigherCorrelations.ComplexFourierRegularity

/-! UNCONDITIONAL regularity and compact support under sector pullback. -/
namespace HigherCorrelations
noncomputable section
open Set

theorem signedConjugate_involutive (j : Fin 6) (z : ℂ) :
    signedConjugate j (signedConjugate j z)=z := by
  simp [signedConjugate]; split_ifs <;> simp_all

theorem signedConjugate_norm (j : Fin 6) (z : ℂ) : ‖signedConjugate j z‖=‖z‖ := by
  unfold signedConjugate
  split_ifs <;> simp

theorem signedPullback_smooth (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin 6) :
    ContDiff ℝ (⊤ : ℕ∞) (signedPullback φ j) := by
  have h := hφ.comp (signedSectorEquiv j).contDiff
  change ContDiff ℝ (⊤ : ℕ∞) (fun p => if j.val<3 then φ (signedSector j p) else star (φ (signedSector j p)))
  split_ifs
  · exact h
  · exact (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp h

theorem signedPullback_compact (φ : ℝ × ℝ → ℂ) (hc : HasCompactSupport φ) (j : Fin 6) :
    HasCompactSupport (signedPullback φ j) := by
  have h := hc.comp_homeomorph (signedSectorEquiv j).toHomeomorph
  change HasCompactSupport (fun p => if j.val<3 then φ (signedSector j p) else star (φ (signedSector j p)))
  split_ifs
  · exact h
  · exact h.comp_left (map_zero (starRingEnd ℂ))

theorem signedPullback_support (φ : ℝ × ℝ → ℂ) (κ : ℝ)
    (hs : tsupport φ ⊆ signedMargin κ) (j : Fin 6) :
    ∀ p ∈ tripleQuadrant, signedPullback φ j p ≠ 0 → p.1+p.2 ≤ 1-κ := by
  intro p hp hn
  have hh : φ (signedSector j p) ≠ 0 := by
    intro hz
    apply hn
    simp [signedPullback,signedConjugate,hz]
  have h := hs (subset_tsupport φ hh)
  change signedGauge (signedSector j p) ≤ 1-κ at h
  rwa [signedGauge_sector j p hp] at h

theorem signed_compact_margin (φ : ℝ × ℝ → ℂ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) : ∃ κ : ℝ, 0<κ ∧ κ<1 ∧ tsupport φ ⊆ signedMargin κ := by
  by_cases hn : (tsupport φ).Nonempty
  · obtain ⟨p,hp,hmax⟩ := hc.exists_isMaxOn hn signedGauge_continuous.continuousOn
    have hp1 : signedGauge p < 1 := hs hp
    refine ⟨(1-signedGauge p)/2,by linarith,by linarith [signedGauge_nonneg p],?_⟩
    intro x hx
    have hh : signedGauge x ≤ signedGauge p := hmax hx
    change signedGauge x ≤ 1-(1-signedGauge p)/2
    linarith
  · exact ⟨1/2,by norm_num,by norm_num,fun p hp => (hn ⟨p,hp⟩).elim⟩

end
end HigherCorrelations
