import HigherCorrelations.TripleQuadrantAxisTrace

/-! UNCONDITIONAL integrated axis trace estimate for a fixed quadrant test. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrant_axis_outside (ψ : ℝ × ℝ → ℂ) (κ : ℝ) (hκ : 0≤κ)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ)
    (r t : ℝ) (hr : 1<r) (ht : 0 ≤ t) : ψ (r,t)=0 := by
  by_contra hn
  have hh := hs (r,t) ⟨by linarith,ht⟩ hn
  dsimp at hh
  linarith

theorem tripleQuadrantAxisScaled_outside (ψ : ℝ × ℝ → ℂ) (κ b : ℝ) (hκ : 0≤κ) (hb : 0<b)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ)
    (r : ℝ) (hr : 1<r) : tripleQuadrantAxisScaled ψ b r=0 := by
  unfold tripleQuadrantAxisScaled
  apply integral_eq_zero_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with t ht
  rw [tripleQuadrant_axis_outside ψ κ hκ hs r (t/b) hr (div_nonneg ht hb.le),zero_mul]
  rfl

theorem tripleQuadrantAxisScaled_outer_integrable (ψ : ℝ × ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (b : ℝ) (hb : 0<b) :
    IntegrableOn (tripleQuadrantAxisScaled ψ b) (Ici 0) := by
  have hi := tripleQuadrantAxisLead_integrable ψ hψ hc b
  rw [IntegrableOn,tripleQuadrant_measure] at hi
  have hh := hi.integral_prod_left
  simpa only [IntegrableOn,tripleQuadrantAxis_scaled_integral ψ b _ hb] using hh

theorem tripleQuadrant_axis_trace_integrable (ψ : ℝ × ℝ → ℂ) (hψ : Continuous ψ)
    (κ : ℝ) (hκ : 0≤κ)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ) :
    IntegrableOn (fun r : ℝ => (r:ℂ)*ψ (r,0)) (Ici 0) := by
  have hi : Integrable ((Icc (0:ℝ) 1).indicator (fun r : ℝ => (r:ℂ)*ψ (r,0))) :=
    (by fun_prop : Continuous (fun r : ℝ => (r:ℂ)*ψ (r,0))).continuousOn.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc
  apply hi.integrableOn.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with r hr
  by_cases hr1 : r≤1
  · rw [indicator_of_mem (show r ∈ Icc (0:ℝ) 1 from ⟨hr,hr1⟩)]
  · rw [indicator_of_notMem (show r ∉ Icc (0:ℝ) 1 from fun h => hr1 h.2),
      tripleQuadrant_axis_outside ψ κ hκ hs r 0 (lt_of_not_ge hr1) le_rfl,mul_zero]

set_option maxHeartbeats 800000 in
theorem tripleQuadrant_axis_integrated_approximation (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (M N b κ : ℝ) (hM : 0≤M) (hN : 0≤N) (hb : 0<b) (hκ : 0≤κ)
    (hbound : ∀ p ∈ tripleQuadrant, ‖ψ p‖≤M)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖≤N)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ) :
    ‖tripleQuadrantAxisLead ψ b-(3/4:ℂ)*(∫ r : ℝ in Ici 0, (r:ℂ)*ψ (r,0))‖≤
      N/(2*b)+M/(4*b) := by
  let C := N/(2*b)+M/(4*b)
  have hC : 0≤C := by dsimp [C]; positivity
  have hi := tripleQuadrantAxisScaled_outer_integrable ψ hψ.continuous hc b hb
  have hj := (tripleQuadrant_axis_trace_integrable ψ hψ.continuous κ hκ hs).const_mul (3/4:ℂ)
  have hg : IntegrableOn ((Icc (0:ℝ) 1).indicator (fun _ : ℝ => C)) (Ici 0) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc).integrableOn
  have hnorm : ∀ᵐ r : ℝ ∂volume.restrict (Ici 0),
      ‖tripleQuadrantAxisScaled ψ b r-(3/4:ℂ)*((r:ℂ)*ψ (r,0))‖ ≤
      (Icc (0:ℝ) 1).indicator (fun _ => C) r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with r hr
    by_cases hr1 : r≤1
    · rw [indicator_of_mem (show r ∈ Icc (0:ℝ) 1 from ⟨hr,hr1⟩)]
      have hh := tripleQuadrantAxis_approximation ψ hψ M N b r hM hN hb hr hbound hD
      rw [mul_assoc] at hh
      apply hh.trans
      have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 hN)
        (show 0≤2*b by positivity)
      dsimp [C]
      simpa only [mul_one] using add_le_add hh' (le_refl (M/(4*b)))
    · rw [indicator_of_notMem (show r ∉ Icc (0:ℝ) 1 from fun h => hr1 h.2),
        tripleQuadrantAxisScaled_outside ψ κ b hκ hb hs r (lt_of_not_ge hr1),
        tripleQuadrant_axis_outside ψ κ hκ hs r 0 (lt_of_not_ge hr1) le_rfl]
      simp
  have hh := norm_integral_le_of_norm_le hg hnorm
  have he : (∫ r : ℝ in Ici 0, (Icc (0:ℝ) 1).indicator (fun _ => C) r)=C := by
    rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr Icc_subset_Ici_self]
    simp [setIntegral_const,Measure.real,Real.volume_Icc]
  rw [he] at hh
  have hsub : (∫ r : ℝ in Ici 0,
      tripleQuadrantAxisScaled ψ b r-(3/4:ℂ)*((r:ℂ)*ψ (r,0))) =
      tripleQuadrantAxisLead ψ b-(3/4:ℂ)*(∫ r : ℝ in Ici 0, (r:ℂ)*ψ (r,0)) := by
    rw [integral_sub hi hj,integral_const_mul,← tripleQuadrantAxis_substitution ψ hψ.continuous hc b hb]
  rw [hsub] at hh
  exact hh

end
end HigherCorrelations
