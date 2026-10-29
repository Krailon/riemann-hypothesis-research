import HigherCorrelations.TripleQuadrantDefinitions
import HigherCorrelations.TripleTestGeometry

/-! UNCONDITIONAL support geometry including both axes and the origin. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrant_closed : IsClosed tripleQuadrant :=
  (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const continuous_snd)

theorem tripleQuadrant_measurable : MeasurableSet tripleQuadrant := tripleQuadrant_closed.measurableSet

theorem tripleQuadrantAmplitude_integrable (ψ : ℝ × ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) : Integrable (tripleQuadrantAmplitude ψ) :=
  (hψ.integrable_of_hasCompactSupport hc).indicator tripleQuadrant_measurable

theorem tripleQuadrantAmplitude_support (ψ : ℝ × ℝ → ℂ) (κ : ℝ)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-κ) :
    Function.support (tripleQuadrantAmplitude ψ) ⊆ tripleQuadrantMargin κ := by
  intro p hp
  change tripleQuadrant.indicator ψ p ≠ 0 at hp
  by_cases hq : p ∈ tripleQuadrant
  · have hn : ψ p ≠ 0 := by simpa [hq] using hp
    exact ⟨hq.1,hq.2,hs p hq hn⟩
  · simp [hq] at hp

theorem tripleQuadrant_scale_range (κ T : ℝ) (p : ℝ × ℝ)
    (hT : 2*Real.pi < T) (hp : p ∈ tripleQuadrantMargin κ) :
    1 ≤ (tripleTestBase T)^p.1 ∧ 1 ≤ (tripleTestBase T)^p.2 ∧
    (tripleTestBase T)^p.1*(tripleTestBase T)^p.2 ≤ (tripleTestBase T)^(1-κ) := by
  have hb := (tripleTestBase_bounds T hT).2.1
  refine ⟨Real.one_le_rpow hb.le hp.1,Real.one_le_rpow hb.le hp.2.1,?_⟩
  rw [← Real.rpow_add (by linarith : 0 < tripleTestBase T)]
  exact Real.rpow_le_rpow_of_exponent_le hb.le hp.2.2

theorem tripleQuadrantMargin_swap (κ : ℝ) (p : ℝ × ℝ) :
    p.swap ∈ tripleQuadrantMargin κ ↔ p ∈ tripleQuadrantMargin κ := by
  simp only [tripleQuadrantMargin,Set.mem_setOf_eq,Prod.fst_swap,Prod.snd_swap]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨h2,h1,by linarith⟩

theorem tripleQuadrantMargin_origin (κ : ℝ) (hκ : κ ≤ 1) :
    (0,0) ∈ tripleQuadrantMargin κ := by exact ⟨le_rfl,le_rfl,by linarith⟩

end
end HigherCorrelations
