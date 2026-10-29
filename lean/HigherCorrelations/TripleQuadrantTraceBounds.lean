import HigherCorrelations.TripleQuadrantSwap

/-! UNCONDITIONAL size bounds for the two limiting axis traces. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrant_axis_trace_bound (ψ : ℝ × ℝ → ℂ) (M κ : ℝ)
    (hM : 0 ≤ M) (hκ : 0 ≤ κ)
    (hbound : ∀ p ∈ tripleQuadrant, ‖ψ p‖ ≤ M)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-κ) :
    ‖∫ r : ℝ in Ici 0, (r:ℂ)*ψ (r,0)‖ ≤ M := by
  have hg : IntegrableOn ((Icc (0:ℝ) 1).indicator (fun _ : ℝ => M)) (Ici 0) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc).integrableOn
  have hh : ∀ᵐ r : ℝ ∂volume.restrict (Ici 0),
      ‖(r:ℂ)*ψ (r,0)‖ ≤ (Icc (0:ℝ) 1).indicator (fun _ => M) r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with r hr
    by_cases hr1 : r ≤ 1
    · rw [indicator_of_mem (show r ∈ Icc (0:ℝ) 1 from ⟨hr,hr1⟩),norm_mul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
      exact (mul_le_mul hr1 (hbound (r,0) ⟨hr,le_rfl⟩) (norm_nonneg _) (by norm_num)).trans_eq (one_mul M)
    · rw [indicator_of_notMem (show r ∉ Icc (0:ℝ) 1 from fun h => hr1 h.2),
        tripleQuadrant_axis_outside ψ κ hκ hs r 0 (lt_of_not_ge hr1) le_rfl]
      simp
  have he : (∫ r : ℝ in Ici 0, (Icc (0:ℝ) 1).indicator (fun _ => M) r)=M := by
    rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr Icc_subset_Ici_self]
    simp [Measure.real,Real.volume_Icc]
  simpa only [he] using norm_integral_le_of_norm_le hg hh

theorem tripleQuadrant_limit_split (ψ : ℝ × ℝ → ℂ) (hψ : Continuous ψ)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-κ) :
    tripleQuadrantLimit ψ = ψ (0,0)/4+
      (3/4:ℂ)*(∫ r : ℝ in Ici 0, (r:ℂ)*ψ (r,0))+
      (3/4:ℂ)*(∫ r : ℝ in Ici 0, (r:ℂ)*ψ (0,r)) := by
  have hi := tripleQuadrant_axis_trace_integrable ψ hψ κ hκ hs
  have hj := tripleQuadrant_axis_trace_integrable (fun p => ψ p.swap)
    (hψ.comp (continuous_snd.prodMk continuous_fst)) κ hκ
    (fun p hp hn => by simpa [add_comm] using hs p.swap ⟨hp.2,hp.1⟩ hn)
  change IntegrableOn (fun r : ℝ => (r:ℂ)*ψ (0,r)) (Ici 0) at hj
  unfold tripleQuadrantLimit
  rw [← integral_Ici_eq_integral_Ioi]
  simp_rw [mul_add]
  rw [integral_add hi hj]
  ring

end
end HigherCorrelations
