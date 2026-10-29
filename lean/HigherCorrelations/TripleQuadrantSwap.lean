import HigherCorrelations.TripleQuadrantAxisLimit

/-! UNCONDITIONAL coordinate exchange, with both axis traces kept separately. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrant_integral_swap (f : ℝ × ℝ → ℂ) :
    (∫ p in tripleQuadrant, f p.swap) = ∫ p in tripleQuadrant, f p := by
  rw [tripleQuadrant_measure]
  exact integral_prod_swap f

theorem tripleQuadrant_swap_smooth (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => ψ p.swap) := by
  exact hψ.comp (contDiff_snd.prodMk contDiff_fst)

theorem tripleQuadrant_swap_compact (ψ : ℝ × ℝ → ℂ) (hc : HasCompactSupport ψ) :
    HasCompactSupport (fun p : ℝ × ℝ => ψ p.swap) :=
  hc.comp_homeomorph (Homeomorph.prodComm ℝ ℝ)

theorem tripleQuadrant_swap_derivative (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (N : ℝ)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖ ≤ N) :
    ∀ p ∈ tripleQuadrant, ‖fderiv ℝ (fun p : ℝ × ℝ => ψ p.swap) p‖ ≤ N := by
  intro p hp
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have he : fderiv ℝ (fun p : ℝ × ℝ => ψ p.swap) p =
      (fderiv ℝ ψ p.swap).comp e.toContinuousLinearMap := by
    exact (((hψ.differentiable (by simp)) p.swap).hasFDerivAt.comp p e.hasFDerivAt).fderiv
  rw [he]
  apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hD p.swap ⟨hp.2,hp.1⟩))
  intro v
  calc
    ‖(fderiv ℝ ψ p.swap).comp e.toContinuousLinearMap v‖ ≤ ‖fderiv ℝ ψ p.swap‖*‖v.swap‖ :=
      (fderiv ℝ ψ p.swap).le_opNorm _
    _ ≤ N*‖v‖ := by
      simpa [Prod.norm_def,max_comm] using mul_le_mul_of_nonneg_right (hD p.swap ⟨hp.2,hp.1⟩) (norm_nonneg v.swap)

theorem tripleQuadrant_second_axis_approximation (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (M N b κ : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N) (hb : 0 < b) (hκ : 0 ≤ κ)
    (hbound : ∀ p ∈ tripleQuadrant, ‖ψ p‖ ≤ M)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖ ≤ N)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-κ) :
    ‖(∫ p in tripleQuadrant, ψ p*(tripleQuadrantAxisKernel b p.swap:ℂ))-
      (3/4:ℂ)*(∫ r : ℝ in Ici 0, (r:ℂ)*ψ (0,r))‖ ≤ N/(2*b)+M/(4*b) := by
  have hh := tripleQuadrant_axis_integrated_approximation (fun p => ψ p.swap)
    (tripleQuadrant_swap_smooth ψ hψ) (tripleQuadrant_swap_compact ψ hc)
    M N b κ hM hN hb hκ (fun p hp => hbound p.swap ⟨hp.2,hp.1⟩)
    (tripleQuadrant_swap_derivative ψ hψ N hD)
    (fun p hp hn => by simpa [add_comm] using hs p.swap ⟨hp.2,hp.1⟩ hn)
  have he := tripleQuadrant_integral_swap (fun p => ψ p*(tripleQuadrantAxisKernel b p.swap:ℂ))
  have he' : tripleQuadrantAxisLead (fun p => ψ p.swap) b =
      ∫ p in tripleQuadrant, ψ p*(tripleQuadrantAxisKernel b p.swap:ℂ) := by
    simpa only [tripleQuadrantAxisLead,Prod.swap_swap] using he
  rw [he'] at hh
  exact hh

end
end HigherCorrelations
