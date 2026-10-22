import HigherCorrelations.PairFourierIdentity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue

/-! UNCONDITIONAL approximate identity estimates. The mass and first absolute
moment are exact on the whole real line, for every positive q. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

private theorem integrable_abs_of_Ioi (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi 0)) : Integrable (fun a : ℝ => f |a|) := by
  have hp : IntegrableOn (fun a : ℝ => f |a|) (Ioi 0) := hf.congr
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha; rw [abs_of_pos ha])
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_,hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def,abs_neg,neg_preimage,neg_Iio,neg_zero] using hp

theorem pairFourierPeak_nonneg (q a : ℝ) (hq : 0≤q) : 0≤pairFourierPeak q a :=
  mul_nonneg hq (Real.exp_pos _).le

theorem pairFourierPeak_integrable (q : ℝ) (hq : 0<q) : Integrable (pairFourierPeak q) := by
  exact (integrable_abs_of_Ioi (fun a => Real.exp (-2*q*a))
    (integrableOn_exp_mul_Ioi (by linarith) 0)).const_mul q

theorem pairFourierPeak_mass (q : ℝ) (hq : 0<q) :
    (∫ a : ℝ, pairFourierPeak q a) = 1 := by
  unfold pairFourierPeak
  rw [integral_const_mul,integral_comp_abs (f := fun a => Real.exp (-2*q*a)),integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero,Real.exp_zero]
  field_simp

theorem pairFourierPeak_moment_integrable (q : ℝ) (hq : 0<q) :
    Integrable (fun a : ℝ => |a| *pairFourierPeak q a) := by
  have hi : IntegrableOn (fun a : ℝ => a*Real.exp (-2*q*a)) (Ioi 0) := by
    simpa only [Real.rpow_one,neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s:=1) (p:=1) (b:=2*q)
        (by norm_num) (by norm_num) (by positivity)
  convert (integrable_abs_of_Ioi _ hi).const_mul q using 1
  funext a
  unfold pairFourierPeak
  ring

theorem pairFourierPeak_moment (q : ℝ) (hq : 0<q) :
    (∫ a : ℝ, |a| *pairFourierPeak q a) = 1/(2*q) := by
  have he : (fun a : ℝ => |a| *pairFourierPeak q a) =
      fun a : ℝ => q*(|a| *Real.exp (-(2*q*|a|))) := by
    funext a; unfold pairFourierPeak; rw [show -2*q*|a| = -(2*q*|a|) by ring]; ring
  rw [he,integral_const_mul,integral_comp_abs (f := fun a => a*Real.exp (-(2*q*a)))]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=2) (r:=2*q) (by norm_num) (by positivity)
  norm_num only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one,Real.rpow_two,
    Real.Gamma_nat_eq_factorial, Nat.factorial_one, Nat.cast_one] at h
  have hg2 : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  rw [h,hg2]
  field_simp

theorem pairFourierPeak_approximation (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (M : ℝ) (hM : ∀ a : ℝ, ‖g a-g 0‖≤M*|a|)
    (q : ℝ) (hq : 0<q) :
    ‖(∫ a : ℝ, g a*(pairFourierPeak q a : ℂ))-g 0‖≤M/(2*q) := by
  have hk := pairFourierPeak_integrable q hq
  have hkC : Integrable (fun a : ℝ => (pairFourierPeak q a : ℂ)) := hk.ofReal
  have hp : Integrable (fun a => g a*(pairFourierPeak q a : ℂ)) :=
    (hg.mul (by unfold pairFourierPeak; fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hz : (∫ a : ℝ, g 0*(pairFourierPeak q a : ℂ)) = g 0 := by
    rw [integral_const_mul,integral_complex_ofReal,pairFourierPeak_mass q hq]
    simp
  have hd : (∫ a : ℝ, g a*(pairFourierPeak q a : ℂ))-g 0 =
      ∫ a : ℝ, g a*(pairFourierPeak q a : ℂ)-g 0*(pairFourierPeak q a : ℂ) := by
    simpa only [hz] using (integral_sub hp (hkC.const_mul (g 0))).symm
  rw [hd]
  have hb : ∀ a : ℝ, ‖g a*(pairFourierPeak q a : ℂ)-g 0*(pairFourierPeak q a : ℂ)‖ ≤
      M*(|a| *pairFourierPeak q a) := by
    intro a
    rw [← sub_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (pairFourierPeak_nonneg q a hq.le)]
    exact (mul_le_mul_of_nonneg_right (hM a) (pairFourierPeak_nonneg q a hq.le)).trans_eq (by ring)
  calc
    _ ≤ ∫ a : ℝ, M*(|a| *pairFourierPeak q a) := norm_integral_le_of_norm_le
      ((pairFourierPeak_moment_integrable q hq).const_mul M) (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul,pairFourierPeak_moment q hq]; ring

theorem pairFourierTest_bounds (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) :
    ∃ M₀ M₁ : ℝ, 0≤M₀ ∧ 0≤M₁ ∧ (∀ a, ‖g a‖≤M₀) ∧
      (∀ a, ‖deriv g a‖≤M₁) ∧ (∀ a : ℝ, ‖g a-g 0‖≤M₁*|a|) := by
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hg.continuous
  obtain ⟨B,hB⟩ := hc.deriv.exists_bound_of_continuous (hg.continuous_deriv (by rfl))
  refine ⟨A,B,(norm_nonneg (g 0)).trans (hA 0),
    (norm_nonneg (deriv g 0)).trans (hB 0),hA,hB,fun a => ?_⟩
  simpa only [sub_zero,Real.norm_eq_abs] using
    convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hg.differentiable (by norm_num) x) (fun x _ => hB x)
      (mem_univ (0:ℝ)) (mem_univ a)

end
end HigherCorrelations
