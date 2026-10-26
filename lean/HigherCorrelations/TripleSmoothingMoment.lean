import HigherCorrelations.TripleSmoothingMomentDefinitions
import HigherCorrelations.TripleBudgetMoments

/-! UNCONDITIONAL. Sharp first smoothing moment, with explicit constant two.
All integrands are shown integrable before splitting the integrals. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem tripleSmoothingMean_continuous (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    Continuous (fun u : ℝ => ω u*Real.log u) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u ∈ tsupport ω
  · have hs := hω.support hu
    exact hω.smooth.continuous.continuousAt.mul
      (Real.continuousAt_log (by linarith [hs.1]))
  · have he : (fun v : ℝ => ω v*Real.log v) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hu] with v hv
      simp [hv]
    exact continuousAt_const.congr_of_eventuallyEq he

theorem tripleSmoothingMean_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    Integrable (fun u : ℝ => ω u*Real.log u) := by
  apply (tripleSmoothingMean_continuous ω hω).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro u hu
  apply tripleBudgetWeight_support ω hω
  intro hz
  exact hu (by simp [hz])

theorem tripleSmoothingMean_manuscript (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    tripleSmoothingMean ω = ∫ u in (1:ℝ)..2, ω u*Real.log u := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have hw : ω u ≠ 0 := by intro hz; exact hu (by simp [hz])
  have hs := hω.support (subset_tsupport ω hw)
  exact ⟨hs.1,hs.2.le⟩

theorem tripleSmoothingMean_bounds (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    0 ≤ tripleSmoothingMean ω ∧ tripleSmoothingMean ω ≤ Real.log 2 := by
  have hi := tripleSmoothingMean_integrable ω hω
  have hw := tripleBudgetWeight_integrable ω hω
  have hlo (u : ℝ) : 0 ≤ ω u*Real.log u := by
    by_cases hz : ω u = 0
    · simp [hz]
    · exact mul_nonneg (hω.nonneg u) (Real.log_nonneg (tripleBudgetWeight_support ω hω hz).1)
  have hhi (u : ℝ) : ω u*Real.log u ≤ ω u*Real.log 2 := by
    by_cases hz : ω u = 0
    · simp [hz]
    · have hs := tripleBudgetWeight_support ω hω hz
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hs.1]) hs.2) (hω.nonneg u)
  refine ⟨integral_nonneg hlo,?_⟩
  have h := integral_mono hi (hw.mul_const _) hhi
  simpa only [integral_mul_const,hω.mass,one_mul,tripleSmoothingMean] using h

/-- Pointwise logarithm identity on the positive smoothing support. -/
theorem tripleSmoothingMoment_log_identity (T u : ℝ) (hT : 0 < T) (hu : 1 ≤ u) :
    Real.log (|T*u|+2)-Real.log T-Real.log u = Real.log (1+2/(T*u)) := by
  have hu0 : 0 < u := by linarith
  rw [abs_of_pos (mul_pos hT hu0)]
  have he : T*u+2 = (T*u)*(1+2/(T*u)) := by field_simp <;> ring
  rw [he,Real.log_mul (mul_ne_zero hT.ne' hu0.ne') (by positivity : 1+2/(T*u) ≠ 0),
    Real.log_mul hT.ne' hu0.ne']
  ring

/-- Uniform in the entire smoothing interval, including its endpoints. -/
theorem tripleSmoothingMoment_log_bounds (T u : ℝ) (hT : 0 < T) (hu : 1 ≤ u) :
    0 ≤ Real.log (1+2/(T*u)) ∧ Real.log (1+2/(T*u)) ≤ 2/T := by
  have hu0 : 0 < u := by linarith
  have hp : 0 ≤ 2/(T*u) := by positivity
  refine ⟨Real.log_nonneg (by linarith),?_⟩
  calc
    _ ≤ (1+2/(T*u))-1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = 2/(T*u) := by ring
    _ ≤ 2/T := div_le_div_of_nonneg_left (by norm_num) hT (by nlinarith)

/-- This difference is globally integrable despite log u being singular at zero. -/
theorem tripleSmoothingMoment_difference_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) : Integrable (fun u : ℝ => ω u*(Real.log (|T*u|+2)-Real.log T-Real.log u)) := by
  have hi := ((tripleBudgetMoment_integrable ω hω T 1).sub
    ((tripleBudgetWeight_integrable ω hω).mul_const (Real.log T))).sub
    (tripleSmoothingMean_integrable ω hω)
  convert hi using 1
  funext u
  simp only [Pi.sub_apply,pow_one]
  ring

theorem tripleSmoothingError_difference_integral (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) : tripleSmoothingError ω T =
      ∫ u : ℝ, ω u*(Real.log (|T*u|+2)-Real.log T-Real.log u) := by
  have hi : Integrable (fun u : ℝ => ω u*Real.log (|T*u|+2)) := by
    simpa only [pow_one] using tripleBudgetMoment_integrable ω hω T 1
  have hw := (tripleBudgetWeight_integrable ω hω).mul_const (Real.log T)
  have he : (fun u : ℝ => ω u*(Real.log (|T*u|+2)-Real.log T-Real.log u)) =
      fun u => (ω u*Real.log (|T*u|+2)-ω u*Real.log T)-ω u*Real.log u := by
    funext u; ring
  rw [he,integral_sub (f := fun u : ℝ => ω u*Real.log (|T*u|+2)-ω u*Real.log T)
    (g := fun u : ℝ => ω u*Real.log u) (hi.sub hw) (tripleSmoothingMean_integrable ω hω),
    integral_sub hi hw,integral_mul_const,hω.mass,one_mul]
  simp only [tripleSmoothingError,tripleBudgetMoment,pow_one,tripleSmoothingMean]

/-- The logarithmic correction integral is absolutely integrable. -/
theorem tripleSmoothingError_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0 < T) : Integrable (fun u : ℝ => ω u*Real.log (1+2/(T*u))) := by
  apply (tripleSmoothingMoment_difference_integrable ω hω T).congr
  filter_upwards [] with u
  by_cases hz : ω u = 0
  · simp [hz]
  · rw [tripleSmoothingMoment_log_identity T u hT (tripleBudgetWeight_support ω hω hz).1]

theorem tripleSmoothingError_integral (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0 < T) : tripleSmoothingError ω T =
      ∫ u : ℝ, ω u*Real.log (1+2/(T*u)) := by
  rw [tripleSmoothingError_difference_integral ω hω T]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hz : ω u = 0
  · simp [hz]
  · rw [tripleSmoothingMoment_log_identity T u hT (tripleBudgetWeight_support ω hω hz).1]

/-- The constant two is independent of the admissible weight. -/
theorem tripleSmoothingError_bounds (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0 < T) : 0 ≤ tripleSmoothingError ω T ∧ tripleSmoothingError ω T ≤ 2/T := by
  have hlo (u : ℝ) : 0 ≤ ω u*Real.log (1+2/(T*u)) := by
    by_cases hz : ω u = 0
    · simp [hz]
    · exact mul_nonneg (hω.nonneg u)
        (tripleSmoothingMoment_log_bounds T u hT (tripleBudgetWeight_support ω hω hz).1).1
  have hhi (u : ℝ) : ω u*Real.log (1+2/(T*u)) ≤ ω u*(2/T) := by
    by_cases hz : ω u = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left
        (tripleSmoothingMoment_log_bounds T u hT (tripleBudgetWeight_support ω hω hz).1).2 (hω.nonneg u)
  rw [tripleSmoothingError_integral ω hω T hT]
  refine ⟨integral_nonneg hlo,?_⟩
  have h := integral_mono (tripleSmoothingError_integrable ω hω T hT)
    ((tripleBudgetWeight_integrable ω hω).mul_const (2/T)) hhi
  simpa only [integral_mul_const,hω.mass,one_mul] using h

/-- Manuscript domain, including T=3, with both constants explicitly bounded. -/
theorem tripleSmoothingMoment_sharp (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3 ≤ T) :
    0 ≤ tripleSmoothingMean ω ∧ tripleSmoothingMean ω ≤ Real.log 2 ∧
    0 ≤ tripleBudgetMoment ω T 1-Real.log T-tripleSmoothingMean ω ∧
    tripleBudgetMoment ω T 1-Real.log T-tripleSmoothingMean ω ≤ 2/T := by
  exact ⟨(tripleSmoothingMean_bounds ω hω).1,(tripleSmoothingMean_bounds ω hω).2,
    tripleSmoothingError_bounds ω hω T (by linarith)⟩

/-- Fix the weight, then let height tend to infinity; no integral-limit exchange. -/
theorem tripleSmoothingMoment_tendsto (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    Tendsto (fun T : ℝ => tripleBudgetMoment ω T 1-Real.log T) atTop (𝓝 (tripleSmoothingMean ω)) := by
  have he : Tendsto (tripleSmoothingError ω) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun T : ℝ => (2:ℝ)/T) atTop (𝓝 0))
    · exact (eventually_ge_atTop (3:ℝ)).mono (fun T hT =>
        (tripleSmoothingError_bounds ω hω T (by linarith)).1)
    · exact (eventually_ge_atTop (3:ℝ)).mono (fun T hT =>
        (tripleSmoothingError_bounds ω hω T (by linarith)).2)
  convert he.add_const (tripleSmoothingMean ω) using 1
  · funext T; unfold tripleSmoothingError; ring
  · simp

end
end HigherCorrelations
