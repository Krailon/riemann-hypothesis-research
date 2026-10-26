import HigherCorrelations.TripleBudgetAccounting

/-! UNCONDITIONAL smoothing moments and the named archimedean-cube error. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudgetWeight_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    Integrable ω :=
  hω.smooth.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (tripleBudgetWeight_support ω hω))

theorem tripleBudgetMoment_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (r : ℕ) : Integrable (fun u : ℝ => ω u*Real.log (|T*u|+2)^r) := by
  have hc : Continuous (fun u : ℝ => ω u*Real.log (|T*u|+2)^r) :=
    hω.smooth.continuous.mul
      ((((continuous_const.mul continuous_id).abs.add_const 2).log (fun _ => by positivity)).pow r)
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro u hu
  apply tripleBudgetWeight_support ω hω
  intro hz
  exact hu (by simp [hz])

theorem tripleBudgetMoment_bounds (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤T) (r : ℕ) :
    Real.log T^r ≤ tripleBudgetMoment ω T r ∧
      tripleBudgetMoment ω T r ≤ Real.log (2*T+2)^r := by
  have hT0 : 0<T := by linarith
  have hq : 0≤Real.log T := Real.log_nonneg (by linarith)
  have hl (u : ℝ) (hu : ω u ≠ 0) :
      Real.log T ≤ Real.log (|T*u|+2) ∧ Real.log (|T*u|+2) ≤ Real.log (2*T+2) := by
    have hs := tripleBudgetWeight_support ω hω hu
    rw [abs_of_nonneg (mul_nonneg hT0.le (by linarith [hs.1]))]
    exact ⟨Real.log_le_log hT0 (by nlinarith [hs.1]),
      Real.log_le_log (by nlinarith [hs.1]) (by nlinarith [hs.2])⟩
  have hlo (u : ℝ) : ω u*Real.log T^r ≤ ω u*Real.log (|T*u|+2)^r := by
    by_cases hu : ω u = 0
    · simp [hu]
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq (hl u hu).1 r) (hω.nonneg u)
  have hhi (u : ℝ) : ω u*Real.log (|T*u|+2)^r ≤ ω u*Real.log (2*T+2)^r := by
    by_cases hu : ω u = 0
    · simp [hu]
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hq.trans (hl u hu).1) (hl u hu).2 r) (hω.nonneg u)
  have hi := tripleBudgetWeight_integrable ω hω
  have him := tripleBudgetMoment_integrable ω hω T r
  constructor
  · have h := integral_mono (hi.mul_const _) him hlo
    simpa [integral_mul_const,hω.mass,tripleBudgetMoment] using h
  · have h := integral_mono him (hi.mul_const _) hhi
    simpa [integral_mul_const,hω.mass,tripleBudgetMoment] using h

theorem tripleBudget_archcube_bounds (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) :
    0 ≤ (tripleBudgetError ω T X Y .archcube).re ∧
    ‖tripleBudgetError ω T X Y .archcube‖ ≤
      (Real.log (2*T+2)^3-Real.log T^3)/(X*Y)^2 := by
  obtain ⟨hlo,hhi⟩ := tripleBudgetMoment_bounds ω hω T hT 3
  have hp : 0 ≤ (tripleBudgetMoment ω T 3-Real.log T^3)/(X*Y)^2 := by positivity
  constructor
  · exact hp
  · simp only [tripleBudgetError,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
    exact div_le_div_of_nonneg_right (sub_le_sub_right hhi _) (sq_nonneg _)

end
end HigherCorrelations
