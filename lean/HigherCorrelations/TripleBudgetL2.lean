import HigherCorrelations.TripleBudgetMoments
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! UNCONDITIONAL weighted Cauchy--Schwarz for the actual probability smoothing. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudget_weight_mass (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) : (∫ t : ℝ, ω (t/T)/T) = 1 := by
  have h := tripleMaster_weight_mass ω T hT
  simpa only [abs_of_nonneg (hω.nonneg _),hω.mass] using h

theorem tripleBudget_weighted_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun t => ω (t/T)/T*f t) := by
  have hc := ((hω.smooth.continuous.comp (continuous_id.div_const T)).div_const T).mul hf
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  apply tripleMaster_support ω (tripleBudgetWeight_support ω hω) T hT
  intro hz
  exact ht (by simp [hz])

theorem tripleBudget_sqrt_weight_memLp (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp (fun t => Real.sqrt (ω (t/T)/T)*‖f t‖) 2 := by
  have hc := (((hω.smooth.continuous.comp (continuous_id.div_const T)).div_const T).sqrt).mul hf.norm
  apply hc.memLp_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  apply tripleMaster_support ω (tripleBudgetWeight_support ω hω) T hT
  intro hz
  exact ht (by simp [hz])

theorem tripleBudgetL2_cauchy (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ t : ℝ, ω (t/T)/T*‖f t‖*‖g t‖) ≤ tripleBudgetL2 ω T f*tripleBudgetL2 ω T g := by
  have hw (t : ℝ) : 0≤ω (t/T)/T := div_nonneg (hω.nonneg _) hT.le
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := fun t => Real.sqrt (ω (t/T)/T)*‖f t‖)
    (g := fun t => Real.sqrt (ω (t/T)/T)*‖g t‖)
    (Filter.Eventually.of_forall (fun _ => by positivity))
    (Filter.Eventually.of_forall (fun _ => by positivity))
    (by simpa using tripleBudget_sqrt_weight_memLp ω hω T hT f hf)
    (by simpa using tripleBudget_sqrt_weight_memLp ω hω T hT g hg)
  have he (t : ℝ) : (Real.sqrt (ω (t/T)/T)*‖f t‖)*(Real.sqrt (ω (t/T)/T)*‖g t‖) =
      ω (t/T)/T*‖f t‖*‖g t‖ := by
    calc
      _ = (Real.sqrt (ω (t/T)/T))^2*‖f t‖*‖g t‖ := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  simpa only [Real.rpow_two,mul_pow,Real.sq_sqrt (hw _),he,← Real.sqrt_eq_rpow,tripleBudgetL2] using h

theorem tripleBudgetL2_sup (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (f : ℝ → ℂ) (hf : Continuous f) (B : ℝ) (hB : 0≤B)
    (hb : ∀ t ∈ Icc T (2*T), ‖f t‖≤B) : tripleBudgetL2 ω T f ≤ B := by
  apply (Real.sqrt_le_left hB).mpr
  have hp (t : ℝ) : ω (t/T)/T*‖f t‖^2 ≤ ω (t/T)/T*B^2 := by
    by_cases hz : ω (t/T)=0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hb t (tripleMaster_support ω (tripleBudgetWeight_support ω hω) T hT hz)) 2)
        (div_nonneg (hω.nonneg _) hT.le)
  have h := integral_mono (tripleBudget_weighted_integrable ω hω T hT _ (hf.norm.pow 2))
    (tripleBudget_weighted_integrable ω hω T hT _ continuous_const) hp
  simpa only [Pi.pow_apply,integral_mul_const,tripleBudget_weight_mass ω hω T hT,one_mul] using h

theorem tripleBudget_integral_norm_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (f g h : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (B : ℝ) (hB : 0≤B) (hb : ∀ t ∈ Icc T (2*T), ‖h t‖≤B) :
    ‖tripleSmoothedIntegral ω T f g h‖ ≤ tripleBudgetL2 ω T f*tripleBudgetL2 ω T g*B := by
  have hw (t : ℝ) : 0≤ω (t/T)/T := div_nonneg (hω.nonneg _) hT.le
  have hp (t : ℝ) : ‖tripleSmoothedIntegrand ω T f g h t‖ ≤ (ω (t/T)/T*‖f t‖*‖g t‖)*B := by
    simp only [tripleSmoothedIntegrand,norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw t)]
    by_cases hz : ω (t/T)=0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (hb t (tripleMaster_support ω (tripleBudgetWeight_support ω hω) T hT hz)) (by positivity [hw t])
  have hi : Integrable (fun t => (ω (t/T)/T*‖f t‖*‖g t‖)*B) := by
    simpa only [Pi.mul_apply,mul_assoc] using (tripleBudget_weighted_integrable ω hω T hT _ (hf.norm.mul hg.norm)).mul_const B
  calc
    _ ≤ ∫ t : ℝ, (ω (t/T)/T*‖f t‖*‖g t‖)*B := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hp)
    _ = (∫ t : ℝ, ω (t/T)/T*‖f t‖*‖g t‖)*B := integral_mul_const B _
    _ ≤ _ := mul_le_mul_of_nonneg_right (tripleBudgetL2_cauchy ω hω T hT f g hf hg) hB

end
end HigherCorrelations
