import HigherCorrelations.PairDigammaBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! UNCONDITIONAL effective digamma remainder on the right half-plane.
Finite sum/integral comparison precedes passage to the limit. -/
namespace HigherCorrelations
noncomputable section
open Complex Filter MeasureTheory
open scoped Topology

private theorem norm_add_real_lower (z : ℂ) (hz : 0 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    ‖z‖+x ≤ Real.sqrt 2 * ‖z+x‖ := by
  have hs := Complex.sq_norm z
  have ht := Complex.sq_norm (z+x)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, add_zero] at hs ht
  have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (‖z‖+x)^2 ≤ (Real.sqrt 2 * ‖z+x‖)^2 := by
    nlinarith [sq_nonneg (‖z‖-x), mul_nonneg hz hx]
  nlinarith [norm_nonneg z, norm_nonneg (z+x), Real.sqrt_nonneg 2,
    mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg (z+x))]

private theorem inverse_interval_bound (z : ℂ) (hz : 0 < z.re)
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (n:ℝ) (n+1)) :
    ‖(z+n)⁻¹-(z+x)⁻¹‖ ≤ 2*(1/(‖z‖+n)-1/(‖z‖+(n+1))) := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hx0 : 0 ≤ x := hn.trans hx.1
  have ha : 0 < ‖z‖ := norm_pos_iff.mpr (by intro he; simp [he] at hz)
  have hzn : z+n ≠ 0 := by intro he; have := congrArg Complex.re he; simp at this; linarith
  have hzx : z+x ≠ 0 := by intro he; have := congrArg Complex.re he; simp at this; linarith
  have hp : (‖z‖+n)*(‖z‖+x) ≤ 2*(‖z+n‖*‖z+x‖) := by
    have h := mul_le_mul (norm_add_real_lower z hz.le n hn)
      (norm_add_real_lower z hz.le x hx0) (by positivity) (by positivity)
    have he : Real.sqrt 2 * ‖z+(n:ℂ)‖ * (Real.sqrt 2 * ‖z+x‖) =
        2*(‖z+n‖*‖z+x‖) := by
      nlinarith [mul_nonneg (norm_nonneg (z+(n:ℂ))) (norm_nonneg (z+x)),
        congrArg (fun a : ℝ => a * (‖z+n‖*‖z+x‖)) (Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num))]
    norm_cast at h
    rwa [he] at h
  rw [← dist_eq_norm, dist_inv_inv₀ hzn hzx, dist_eq_norm]
  have hd : ‖z+(n:ℂ)-(z+x)‖ = x-n := by
    have he : z+(n:ℂ)-(z+x) = ((n:ℝ)-x : ℝ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hx.1)]
    ring
  rw [hd]
  calc
    _ ≤ 2*(x-n)/((‖z‖+n)*(‖z‖+x)) := by
      apply (div_le_div_iff₀ (mul_pos (norm_pos_iff.mpr hzn) (norm_pos_iff.mpr hzx))
        (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hx.1)]
    _ = 2*(1/(‖z‖+n)-1/(‖z‖+x)) := by field_simp; ring
    _ ≤ _ := by
      have h := one_div_le_one_div_of_le (by positivity : 0 < ‖z‖+x)
        (show ‖z‖+x ≤ ‖z‖+(n+1) by linarith [hx.2])
      linarith

private theorem integral_inverse_eq_log (z : ℂ) (hz : 0 < z.re)
    (n : ℕ) :
    (∫ x : ℝ in (n:ℝ)..(n+1), (z+x)⁻¹) = log (z+(n+1))-log (z+n) := by
  have hne : ∀ x ∈ Set.uIcc (n:ℝ) (n+1), z+x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    intro he
    have := congrArg Complex.re he
    simp at this
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith [hx.1]
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => log (z+x)) (f' := fun x : ℝ => (z+x)⁻¹) ?_ ?_ using 1 <;> try { push_cast; rfl }
  · intro x hx
    have hslit : z+x ∈ slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      rw [Set.uIcc_of_le (by linarith)] at hx
      simp only [Complex.add_re, Complex.ofReal_re]
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith [hx.1]
    simpa using ((hasDerivAt_log hslit).comp (x:ℂ)
      ((hasDerivAt_id (x:ℂ)).const_add z)).comp_ofReal
  · exact (ContinuousOn.inv₀ (by fun_prop) hne).intervalIntegrable

theorem pairDigamma_unit_comparison (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ‖(z+n)⁻¹-(log (z+(n+1))-log (z+n))‖ ≤
      2*(1/(‖z‖+n)-1/(‖z‖+(n+1))) := by
  rw [← integral_inverse_eq_log z hz n]
  have hi : IntervalIntegrable (fun x : ℝ => (z+x)⁻¹) volume n (n+1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx he
    rw [Set.uIcc_of_le (by linarith)] at hx
    have := congrArg Complex.re he
    simp at this
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith [hx.1]
  have hc : (∫ x : ℝ in (n:ℝ)..(n+1), (z+n)⁻¹-(z+x)⁻¹) =
      (z+n)⁻¹-∫ x : ℝ in (n:ℝ)..(n+1), (z+x)⁻¹ := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    simp
  rw [← hc]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (n:ℝ)) (b := n+1) (fun x hx => inverse_interval_bound z hz n x (by
      rw [Set.uIoc_of_le (by linarith)] at hx
      exact ⟨hx.1.le,hx.2⟩))
  simpa using h

theorem pairDigamma_finite_comparison (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, (z+n)⁻¹) - (log (z+N)-log z)‖ ≤
      2*(1/‖z‖-1/(‖z‖+N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have he : (∑ n ∈ Finset.range N, (z+n)⁻¹)+(z+N)⁻¹ - (log (z+(N+1:ℕ))-log z) =
        ((∑ n ∈ Finset.range N, (z+n)⁻¹)-(log (z+N)-log z)) +
        ((z+N)⁻¹-(log (z+(N+1))-log (z+N))) := by push_cast; ring
    rw [he]
    have h := (norm_add_le _ _).trans (add_le_add ih (pairDigamma_unit_comparison z hz N))
    push_cast
    convert h using 1 <;> ring

private theorem log_shift_tendsto (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => log (z+N)-(Real.log (N+1:ℝ):ℂ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => ((N+1:ℝ))⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hic := Complex.continuous_ofReal.continuousAt.tendsto.comp hi
  have hr : Tendsto (fun N : ℕ => 1+(z-1)*((N+1:ℂ))⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hic))
  have hl := ((Complex.differentiableAt_log (by simp : (1:ℂ) ∈ slitPlane)).continuousAt).tendsto.comp hr
  simp only [Complex.log_one] at hl
  apply hl.congr'
  apply Filter.Eventually.of_forall
  intro N
  have hp : 0 < (N+1:ℝ) := by positivity
  have hne : z+N ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    have hn := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hnp : (N+1:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have he : 1+(z-1)*(N+1:ℂ)⁻¹ = (z+N)/(N+1:ℂ) := by field_simp; ring
  dsimp only [Function.comp_apply]
  rw [he]
  have hm := Complex.log_mul_ofReal (N+1:ℝ) hp ((z+N)/(N+1:ℂ)) (div_ne_zero hne hnp)
  push_cast at hm
  rw [div_mul_cancel₀ _ hnp] at hm
  linear_combination -hm

theorem pairDigamma_remainder_bound (z : ℂ) (hz : 0 < z.re) :
    ‖digamma z-log z‖ ≤ 2/‖z‖ := by
  have hs := (Complex.hasSum_digamma_of_re_pos hz).tendsto_sum_nat
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
    Real.tendsto_harmonic_sub_log_add_one
  have hl := log_shift_tendsto z hz
  have hc : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, (z+n)⁻¹)-(log (z+N)-log z)) atTop
      (𝓝 (log z-digamma z)) := by
    have h := ((hh.sub hs).sub hl).add_const (log z)
    convert h using 1
    · ext N
      simp only [Function.comp_apply, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_inv,
        Complex.ofReal_natCast, Finset.sum_sub_distrib]
      push_cast
      ring
    · push_cast
      ring
  have hb : ∀ N : ℕ,
      ‖(∑ n ∈ Finset.range N, (z+n)⁻¹)-(log (z+N)-log z)‖ ≤ 2/‖z‖ := by
    intro N
    have h := pairDigamma_finite_comparison z hz N
    have hp : 0 ≤ 1/(‖z‖+(N:ℝ)) := by positivity
    calc
      _ ≤ 2*(1/‖z‖-1/(‖z‖+N)) := h
      _ ≤ 2/‖z‖ := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
          (sub_le_self (1/‖z‖) hp) (show (0:ℝ) ≤ 2 by norm_num)
  have h := le_of_tendsto hc.norm (Filter.Eventually.of_forall hb)
  rwa [norm_sub_rev] at h

end
end HigherCorrelations
