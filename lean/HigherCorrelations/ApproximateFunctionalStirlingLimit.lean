import HigherCorrelations.ApproximateFunctionalStirlingSeries
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! UNCONDITIONAL identification of the convergent logarithmic correction
with the actual Gamma function. The normalization comes from real Stirling,
not from an assumed vertical-strip Gamma asymptotic. -/
namespace HigherCorrelations
noncomputable section
open Complex Filter
open scoped Topology

theorem afeStirling_finite_logs (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ∑ n ∈ Finset.range N, log (z+n) = afeStirlingMain (z+N)-afeStirlingMain z -
      ∑ n ∈ Finset.range N, afeStirlingStep (z+n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h := afeStirlingMain_increment (z+N) (by simp only [add_re, natCast_re]; positivity)
    have he : z+(N+1:ℕ) = (z+N)+1 := by push_cast; ring
    rw [he]
    linear_combination -h

theorem afe_logGammaSeq_decomposition (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    logGammaSeq z N = afeStirlingMain z +
      (z*(Real.log N:ℂ)+(Real.log (N.factorial):ℂ)-afeStirlingMain (z+N+1)) +
      ∑ n ∈ Finset.range (N+1), afeStirlingStep (z+n) := by
  rw [logGammaSeq, afeStirling_finite_logs z hz]
  push_cast; ring

theorem afe_scaled_log_limit (v : ℂ) :
    Tendsto (fun n : ℕ => (n+1:ℂ)*log (1+v/(n+1:ℂ))) atTop (𝓝 v) := by
  have hi : Tendsto (fun n : ℕ => (n+1:ℝ)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hic : Tendsto (fun n : ℕ => (n+1:ℂ)⁻¹) atTop (𝓝 (0:ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hi
  have hi' : Tendsto (fun n : ℕ => (n+1:ℂ)⁻¹) atTop (𝓝[≠] (0:ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hic, Filter.Eventually.of_forall (fun n => by
      change (n+1:ℂ)⁻¹ ≠ 0
      apply inv_ne_zero
      exact_mod_cast (show (n:ℝ)+1 ≠ 0 by positivity))⟩
  have hd : HasDerivAt (fun w : ℂ => log (1+v*w)) v 0 := by
    have h₁ : HasDerivAt (fun w : ℂ => 1+v*w) v 0 := by
      simpa using (((hasDerivAt_id (0:ℂ)).const_mul v).const_add 1)
    have h₂ : HasDerivAt log (1+v*0)⁻¹ (1+v*0) :=
      Complex.hasDerivAt_log (by simp)
    have h := h₂.comp 0 h₁
    convert! h using 1 <;> simp [Function.comp_def]
  simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using hd.tendsto_slope_zero.comp hi'

theorem afe_small_log_limit (v : ℂ) :
    Tendsto (fun n : ℕ => log (1+v/(n+1:ℂ))) atTop (𝓝 (0:ℂ)) := by
  have hi : Tendsto (fun n : ℕ => (n+1:ℝ)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hic : Tendsto (fun n : ℕ => (n+1:ℂ)⁻¹) atTop (𝓝 (0:ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hi
  have harg : Tendsto (fun n : ℕ => 1+v/(n+1:ℂ)) atTop (𝓝 (1:ℂ)) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (tendsto_const_nhds.mul hic)
  simpa only [Function.comp_def, Complex.log_one] using
    ((Complex.hasDerivAt_log (by simp : (1:ℂ) ∈ slitPlane)).continuousAt.tendsto.comp harg)

theorem afeStirling_offset_limit (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => z*(Real.log (n+1:ℝ):ℂ) +
      (Real.log ((n+1).factorial):ℂ) - afeStirlingMain (z+(n+1:ℕ)+1))
      atTop (𝓝 ((Real.log (2*Real.pi)/2:ℝ):ℂ)) := by
  have hs : Tendsto (fun n : ℕ => (Real.log (Stirling.stirlingSeq (n+1)):ℂ)) atTop
      (𝓝 ((Real.log (Real.sqrt Real.pi):ℝ):ℂ)) := by
    have h := (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).comp
      (tendsto_add_atTop_nat 1)
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp h
  have hlog := afe_scaled_log_limit (z+1)
  have hsmall := afe_small_log_limit (z+1)
  have ht := (hs.add_const ((Real.log 2/2:ℝ):ℂ)).add_const (z+1)
  have ht' := ht.sub (hlog.add (tendsto_const_nhds.mul hsmall (a := z+1-1/2)))
  have hc : ((Real.log (Real.sqrt Real.pi):ℝ):ℂ) + ((Real.log 2/2:ℝ):ℂ) + (z+1) -
      ((z+1)+(z+1-1/2)*0) = ((Real.log (2*Real.pi)/2:ℝ):ℂ) := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_ne_zero]
    push_cast; ring
  rw [hc] at ht'
  apply ht'.congr'
  apply Filter.Eventually.of_forall
  intro n
  have ha : 0 < (n+1:ℝ) := by positivity
  have haC : (n+1:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hv : z+(n+1:ℕ)+1 ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hmul : (1+(z+1)/(n+1:ℂ))*(n+1:ℂ) = z+(n+1:ℕ)+1 := by
    push_cast; field_simp; ring
  have hn : 1+(z+1)/(n+1:ℂ) ≠ 0 := by
    intro he
    apply hv
    rw [← hmul, he, zero_mul]
  have he := Complex.log_mul_ofReal (n+1:ℝ) ha (1+(z+1)/(n+1:ℂ)) hn
  push_cast at he
  rw [hmul] at he
  dsimp only [Function.comp_apply]
  rw [afeStirlingMain, he, Stirling.log_stirlingSeq_formula]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) ha.ne',
    Real.log_div ha.ne' (Real.exp_pos 1).ne', Real.log_exp]
  push_cast
  ring

theorem afe_logGammaSeq_limit (z : ℂ) (hz : 0 < z.re) (hnorm : 2 ≤ ‖z‖) :
    Tendsto (fun n : ℕ => logGammaSeq z (n+1)) atTop
      (𝓝 (afeStirlingMain z + ((Real.log (2*Real.pi)/2:ℝ):ℂ) + afeStirlingCorrection z)) := by
  have hs := (afeStirlingStep_summable_norm z hz.le hnorm).of_norm.hasSum.tendsto_sum_nat
  have ht := ((tendsto_const_nhds (x := afeStirlingMain z)).add (afeStirling_offset_limit z hz)).add
    (hs.comp (tendsto_add_atTop_nat 2))
  convert ht using 1
  · ext n
    rw [afe_logGammaSeq_decomposition z hz]
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, Nat.add_assoc]
  · rfl

theorem afeGamma_stirling_identity (z : ℂ) (hz : 0 < z.re) (hnorm : 2 ≤ ‖z‖) :
    Gamma z = exp (afeStirlingMain z + ((Real.log (2*Real.pi)/2:ℝ):ℂ) +
      afeStirlingCorrection z) := by
  have h := (Complex.continuous_exp.tendsto _).comp (afe_logGammaSeq_limit z hz hnorm)
  have he : (fun n : ℕ => exp (logGammaSeq z (n+1))) = (fun n : ℕ => GammaSeq z (n+1)) := by
    funext n
    exact exp_logGammaSeq hz (by omega)
  change Tendsto (fun n : ℕ => exp (logGammaSeq z (n+1))) _ _ at h
  rw [he] at h
  exact tendsto_nhds_unique ((GammaSeq_tendsto_Gamma z).comp (tendsto_add_atTop_nat 1)) h

end
end HigherCorrelations
