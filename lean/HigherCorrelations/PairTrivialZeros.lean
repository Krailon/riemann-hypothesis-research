import HigherCorrelations.PairContourResidues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Simplicity of the trivial zeros, derived from the functional equation.
UNCONDITIONAL. This concerns only -2,-4,..., never the nontrivial zeros. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

private def reflectedFactor (z : ℂ) : ℂ :=
  2 * Complex.exp (Complex.log (2*(Real.pi:ℂ)) * (-(1-z))) *
    Complex.Gamma (1-z) * riemannZeta (1-z)

private theorem reflectedFactor_ne (z : ℂ) (hz : z.re < 0) : reflectedFactor z ≠ 0 := by
  have hw : 1 < (1-z).re := by simp; linarith
  have hn : ∀ m : ℕ, (1-z) ≠ -(m:ℂ) := by
    intro m he
    have hr := congrArg Complex.re he
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
    (Complex.Gamma_ne_zero hn)) (riemannZeta_ne_zero_of_one_lt_re hw)

private theorem reflectedFactor_diff (z : ℂ) (hz : z.re < 0) :
    DifferentiableAt ℂ reflectedFactor z := by
  have hn : ∀ m : ℕ, (1-z) ≠ -(m:ℂ) := by
    intro m he
    have hr := congrArg Complex.re he
    simp at hr
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have h1 : 1-z ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  unfold reflectedFactor
  have he : DifferentiableAt ℂ
      (fun w : ℂ => 2 * Complex.exp (Complex.log (2*(Real.pi:ℂ)) * (-(1-w)))) z := by fun_prop
  exact (he.mul ((Complex.differentiableAt_Gamma _ hn).comp z
    (by fun_prop))).mul ((differentiableAt_riemannZeta h1).comp z (by fun_prop))

private theorem zeta_eq_reflectedFactor (z : ℂ) (hz : z.re < 0) :
    riemannZeta z = reflectedFactor z * Complex.cos ((Real.pi:ℂ)*(1-z)/2) := by
  have hn : ∀ m : ℕ, (1-z) ≠ -(m:ℂ) := by
    intro m he
    have hr := congrArg Complex.re he
    simp at hr
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have h1 : 1-z ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hf := riemannZeta_one_sub hn h1
  rw [show 1-(1-z) = z by ring] at hf
  rw [hf, reflectedFactor, Complex.cpow_def_of_ne_zero
    (by exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem pairTrivialZero_deriv_ne_zero (n : ℕ) :
    deriv riemannZeta (-2*(n+1:ℂ)) ≠ 0 := by
  let z : ℂ := -2*(n+1:ℂ)
  have hz : z.re < 0 := by dsimp [z]; simp; positivity
  have ha := reflectedFactor_ne z hz
  have hzero : riemannZeta z = 0 := riemannZeta_neg_two_mul_nat_add_one n
  have hcos : Complex.cos ((Real.pi:ℂ)*(1-z)/2) = 0 := by
    rw [zeta_eq_reflectedFactor z hz] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left ha
  have hsin : Complex.sin ((Real.pi:ℂ)*(1-z)/2) ≠ 0 := by
    intro hs
    have hid := Complex.sin_sq_add_cos_sq ((Real.pi:ℂ)*(1-z)/2)
    simp [hcos, hs] at hid
  have he : riemannZeta =ᶠ[𝓝 z]
      fun w => reflectedFactor w * Complex.cos ((Real.pi:ℂ)*(1-w)/2) := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz] with w hw
    exact zeta_eq_reflectedFactor w hw
  have hc : HasDerivAt (fun w : ℂ => Complex.cos ((Real.pi:ℂ)*(1-w)/2))
      (-Complex.sin ((Real.pi:ℂ)*(1-z)/2) * (-(Real.pi:ℂ)/2)) z := by
    simpa [Function.comp_def] using ((Complex.hasDerivAt_cos _).comp z
      (((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)).const_mul (Real.pi:ℂ) |>.div_const 2))
  have hp := (reflectedFactor_diff z hz).hasDerivAt.mul hc
  have hd := he.deriv_eq.trans hp.deriv
  rw [hcos, mul_zero, zero_add] at hd
  change deriv riemannZeta z ≠ 0
  rw [hd]
  exact mul_ne_zero ha (mul_ne_zero (neg_ne_zero.mpr hsin)
    (div_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num)))

theorem pairTrivialZero_order (n : ℕ) :
    meromorphicOrderAt riemannZeta (-2*(n+1:ℂ)) = (1:ℤ) := by
  have hn : (-2*(n+1:ℂ)) ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have ha := analyticOn_riemannZeta _ hn
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (riemannZeta_neg_two_mul_nat_add_one n) (pairTrivialZero_deriv_ne_zero n)]
  rfl

theorem pairContour_residue_trivial (X t : ℝ) (n : ℕ) :
    residue (pairContourIntegrand X t) (-2*(n+1:ℂ)) = -pairTrivialTerm n (X,t) := by
  have hp : (-2*(n+1:ℂ)) ≠ pairSpectralPoint t+1 := by
    intro he
    have hh := congrArg Complex.re he
    simp [pairSpectralPoint] at hh
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hm : (-2*(n+1:ℂ)) ≠ pairSpectralPoint t-1 := by
    intro he
    have hh := congrArg Complex.re he
    simp [pairSpectralPoint] at hh
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [pairContour_residue_of_order X t _ 1 (pairTrivialZero_order n) hp hm,
    pairContourKernel_trivial]
  simp

end
end HigherCorrelations
