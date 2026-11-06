import HigherCorrelations.ProfileLocalNormalizationDefinitions
import HigherCorrelations.RationalTransfer
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! UNCONDITIONAL exact local normalization and its scalar coefficient limit.
The identity requires T>2pi. No tuple sum, integral or critical-line assertion
about the zero population is used or obtained. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem criticalLocalNormalization_denominators (T : ℝ) (hT : 2*Real.pi<T) :
    0<T ∧ 0<Real.log T ∧ 0 < meanSpacing T := by
  exact ⟨lt_trans (by positivity) hT, (transfer_log_pos T hT).1, meanSpacing_pos T hT⟩

theorem criticalLocalNormalization_identity (T : ℝ) (hT : 2*Real.pi<T) :
    (8/(T*Real.log T))*(3*Real.pi/8)=
      criticalLocalCoefficient T*(1/(T*meanSpacing T)) := by
  have ht : T≠0 := (criticalLocalNormalization_denominators T hT).1.ne'
  have hl : Real.log T≠0 := (transfer_log_pos T hT).1.ne'
  have hq : Real.log (T/(2*Real.pi))≠0 := (transfer_log_pos T hT).2.ne'
  have hp : Real.pi≠0 := Real.pi_ne_zero
  unfold criticalLocalCoefficient meanSpacing
  generalize Real.log T = a at hl ⊢
  generalize Real.log (T/(2*Real.pi)) = b at hq ⊢
  field_simp [ht,hl,hq,hp]
  <;> ring

theorem criticalLocalNormalization_complex (T : ℝ) (hT : 2*Real.pi<T) :
    (8/((T:ℂ)*Real.log T))*kernelBenchmark=
      (criticalLocalCoefficient T:ℂ)*ordinateCoefficient T := by
  have h := congrArg (fun x : ℝ => (x:ℂ)) (criticalLocalNormalization_identity T hT)
  simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,
    Complex.ofReal_one,kernelBenchmark,ordinateCoefficient] using h

theorem criticalLocalCoefficient_transferRatio (T : ℝ) :
    (criticalLocalCoefficient T:ℂ)=(3/2:ℂ)*transferRatio T := by
  unfold criticalLocalCoefficient transferRatio
  push_cast
  ring

theorem criticalLocalNormalization_transferCoefficient (T : ℝ) :
    (8/((T:ℂ)*Real.log T))=(3/2:ℂ)*transferCoefficient T := by
  unfold transferCoefficient
  ring

theorem criticalLocalCoefficient_sub_log (T : ℝ) (hT : 2*Real.pi<T) :
    criticalLocalCoefficient T=(3/2:ℝ)-3*Real.log (2*Real.pi)/(2*Real.log T) := by
  have ht : T≠0 := (criticalLocalNormalization_denominators T hT).1.ne'
  have hc : 2*Real.pi≠0 := by positivity
  have hl : Real.log T≠0 := (transfer_log_pos T hT).1.ne'
  unfold criticalLocalCoefficient
  rw [Real.log_div ht hc]
  field_simp
  <;> ring

theorem criticalLocalCoefficient_bounds (T : ℝ) (hT : 2*Real.pi<T) :
    0<criticalLocalCoefficient T ∧ criticalLocalCoefficient T<(3/2:ℝ) := by
  have hl := (transfer_log_pos T hT).1
  have hq := (transfer_log_pos T hT).2
  have hc : 0<Real.log (2*Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  constructor
  · unfold criticalLocalCoefficient
    positivity
  · rw [criticalLocalCoefficient_sub_log T hT]
    exact sub_lt_self _ (by positivity)

theorem criticalLocalCoefficient_error (T : ℝ) (hT : 2*Real.pi<T) :
    |criticalLocalCoefficient T-(3/2:ℝ)|=3*Real.log (2*Real.pi)/(2*Real.log T) := by
  have hl := (transfer_log_pos T hT).1
  have hc : 0<Real.log (2*Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  rw [criticalLocalCoefficient_sub_log T hT,sub_sub_cancel_left,abs_neg,
    abs_of_pos (by positivity)]

theorem criticalLocalCoefficient_tendsto :
    Tendsto criticalLocalCoefficient atTop (𝓝 (3/2:ℝ)) := by
  have hz : Tendsto (fun T : ℝ => (3*Real.log (2*Real.pi)/2)/Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := (tendsto_const_nhds.sub hz : Tendsto
    (fun T : ℝ => (3/2:ℝ)-(3*Real.log (2*Real.pi)/2)/Real.log T) atTop (𝓝 ((3/2:ℝ)-0)))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
  rw [criticalLocalCoefficient_sub_log T hT]
  ring

theorem criticalLocalCoefficient_complex_tendsto :
    Tendsto (fun T => (criticalLocalCoefficient T:ℂ)) atTop (𝓝 (3/2:ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp criticalLocalCoefficient_tendsto
  simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_ofNat] using h

theorem criticalLocalCoefficient_endpoint : criticalLocalCoefficient (2*Real.pi)=0 := by
  simp [criticalLocalCoefficient,Real.pi_ne_zero]

theorem criticalLocalNormalization_endpoint_spacing : meanSpacing (2*Real.pi)=0 := by
  simp [meanSpacing,Real.pi_ne_zero]

theorem criticalLocalNormalization_endpoint_excluded :
    (8/((2*Real.pi)*Real.log (2*Real.pi)))*(3*Real.pi/8) ≠
      criticalLocalCoefficient (2*Real.pi)*(1/((2*Real.pi)*meanSpacing (2*Real.pi))) := by
  rw [criticalLocalCoefficient_endpoint,zero_mul]
  have hc : 0<Real.log (2*Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  exact ne_of_gt (by positivity)

end
end HigherCorrelations
