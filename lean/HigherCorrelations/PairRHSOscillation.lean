import HigherCorrelations.PairRHSArchIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! UNCONDITIONAL oscillatory logarithmic integral, with its closed height endpoint. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem pairRHS_log_integrals (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => Real.log (t+2)) (Set.uIcc 0 T) ∧
    ContinuousOn (fun t : ℝ => (t+2)⁻¹) (Set.uIcc 0 T) ∧
    (∫ t in (0:ℝ)..T, (t+2)⁻¹) = Real.log (T+2)-Real.log 2 := by
  have hp : ∀ t ∈ Set.uIcc 0 T, t+2 ≠ 0 := by
    intro t ht; rw [Set.uIcc_of_le hT] at ht; linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => Real.log (t+2)) (Set.uIcc 0 T) :=
    (continuousOn_id.add continuousOn_const).log hp
  have hi : ContinuousOn (fun t : ℝ => (t+2)⁻¹) (Set.uIcc 0 T) :=
    (continuousOn_id.add continuousOn_const).inv₀ hp
  refine ⟨hc,hi,?_⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => by
      simpa only [mul_one] using (Real.hasDerivAt_log (hp t ht)).comp t
        ((hasDerivAt_id t).add_const 2)) hi.intervalIntegrable
  simpa using he

theorem pairRHS_log_oscillation (ω T : ℝ) (hω : 0 < ω) (hT : 0 ≤ T) :
    ‖∫ t in (0:ℝ)..T, (Real.log (t+2):ℂ)*Complex.exp (-Complex.I*ω*t)‖ ≤
      2*Real.log (T+2)/ω := by
  let v : ℝ → ℂ := fun t => Complex.exp (-Complex.I*ω*t)/(-Complex.I*ω)
  have hw : (-Complex.I*(ω:ℂ)) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hω.ne')
  obtain ⟨hlog,hinv,he⟩ := pairRHS_log_integrals T hT
  have hvc : Continuous v := by unfold v; fun_prop
  have hdc (t : ℝ) : HasDerivAt v (Complex.exp (-Complex.I*ω*t)) t := by
    have h := ((((hasDerivAt_id t).ofReal_comp).const_mul (-Complex.I*ω)).cexp).div_const (-Complex.I*ω)
    simpa only [id_eq,Complex.ofReal_one,mul_one,mul_div_cancel_right₀ _ hw] using h
  have hul : ContinuousOn (fun t : ℝ => (Real.log (t+2):ℂ)) (Set.uIcc 0 T) :=
    Complex.continuous_ofReal.comp_continuousOn hlog
  have hui : ContinuousOn (fun t : ℝ => (((t+2)⁻¹:ℝ):ℂ)) (Set.uIcc 0 T) :=
    Complex.continuous_ofReal.comp_continuousOn hinv
  have hib := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hul hvc.continuousOn (u' := fun t : ℝ => (((t+2)⁻¹:ℝ):ℂ))
    (v' := fun t : ℝ => Complex.exp (-Complex.I*ω*t)) (by
      intro t ht
      have hp : t+2 ≠ 0 := by rw [min_eq_left hT,max_eq_right hT] at ht; linarith [ht.1]
      convert ((Real.hasDerivAt_log hp).comp t
        ((hasDerivAt_id t).add_const 2)).ofReal_comp using 1 <;> simp [Function.comp_def])
    (fun t _ => hdc t) hui.intervalIntegrable
    ((show Continuous (fun t : ℝ => Complex.exp (-Complex.I*ω*t)) by fun_prop).intervalIntegrable 0 T)
  have hvnorm (t : ℝ) : ‖v t‖ = 1/ω := by
    simp [v,norm_div,norm_mul,Complex.norm_exp,Complex.mul_re,
      abs_of_pos hω]
  have hrem : ‖∫ t in (0:ℝ)..T, (((t+2)⁻¹:ℝ):ℂ)*v t‖ ≤
      (Real.log (T+2)-Real.log 2)/ω := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hT
      (f := fun t => (((t+2)⁻¹:ℝ):ℂ)*v t) (g := fun t => (t+2)⁻¹/ω)
      (by
        filter_upwards [] with t ht
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,hvnorm]
        rw [abs_of_nonneg (inv_nonneg.mpr (by linarith [ht.1.le]))]
        simp only [div_eq_mul_inv,one_mul]; exact le_rfl)
      (hinv.intervalIntegrable.div_const ω)
    simpa only [intervalIntegral.integral_div,he] using hb
  rw [hib]
  calc
    _ ≤ ‖(Real.log (T+2):ℂ)*v T‖+‖(Real.log (0+2):ℂ)*v 0‖+
        ‖∫ t in (0:ℝ)..T, (((t+2)⁻¹:ℝ):ℂ)*v t‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ Real.log (T+2)/ω+Real.log 2/ω+(Real.log (T+2)-Real.log 2)/ω := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,hvnorm,zero_add]
      rw [abs_of_nonneg (Real.log_nonneg (by linarith)),abs_of_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
      simpa only [div_eq_mul_inv,one_mul] using add_le_add le_rfl hrem
    _ = _ := by ring

end
end HigherCorrelations
