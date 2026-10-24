import HigherCorrelations.FourierDecayDefinitions
import HigherCorrelations.PairMeanFourierRules
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-! UNCONDITIONAL finite-order Fourier decay with exact constants.
The nonzero-frequency quotient is derived only after a global power bound. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped FourierTransform

theorem fourierDecay_derivative_support (f : ℝ → ℂ) (N : ℕ) :
    tsupport (iteratedDeriv N f) ⊆ tsupport f := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem fourierDecay_derivative_compact (f : ℝ → ℂ) (hc : HasCompactSupport f) (N : ℕ) :
    HasCompactSupport (iteratedDeriv N f) := by
  induction N with
  | zero => simpa using hc
  | succ N ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem fourierDecay_derivative_integrable (f : ℝ → ℂ) (N : ℕ)
    (hf : ContDiff ℝ N f) (hc : HasCompactSupport f) (j : ℕ) (hj : j≤N) :
    Integrable (iteratedDeriv j f) :=
  (hf.continuous_iteratedDeriv j (by exact_mod_cast hj)).integrable_of_hasCompactSupport
    (fourierDecay_derivative_compact f hc j)

/-- The sign is positive after transforming the derivative. -/
theorem pairMeanFourier_iteratedDeriv (f : ℝ → ℂ) (N : ℕ)
    (hf : ContDiff ℝ N f) (hc : HasCompactSupport f) (ξ : ℝ) :
    pairMeanFourier (iteratedDeriv N f) ξ =
      (2*(Real.pi:ℂ)*Complex.I*ξ)^N * pairMeanFourier f ξ := by
  rw [pairMeanFourier_eq,pairMeanFourier_eq]
  have he := Real.fourier_iteratedDeriv (N := (N:ℕ∞)) hf
    (fun j hj => fourierDecay_derivative_integrable f N hf hc j (by exact_mod_cast hj))
    (n := N) le_rfl
  exact congrFun he ξ

theorem pairMeanFourier_power_bound (f : ℝ → ℂ) (N : ℕ)
    (hf : ContDiff ℝ N f) (hc : HasCompactSupport f) (ξ : ℝ) :
    (2*Real.pi*|ξ|)^N * ‖pairMeanFourier f ξ‖ ≤ ∫ u : ℝ, ‖iteratedDeriv N f u‖ := by
  have he := pairMeanFourier_norm_bound (iteratedDeriv N f) ξ
  rw [pairMeanFourier_iteratedDeriv f N hf hc ξ] at he
  simpa only [norm_mul,norm_pow,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_ofNat,abs_of_pos Real.pi_pos,mul_one] using he

theorem pairMeanFourier_decay (f : ℝ → ℂ) (N : ℕ)
    (hf : ContDiff ℝ N f) (hc : HasCompactSupport f) (ξ : ℝ) (hξ : ξ≠0) :
    ‖pairMeanFourier f ξ‖ ≤ (∫ u : ℝ, ‖iteratedDeriv N f u‖)/(2*Real.pi*|ξ|)^N := by
  apply (le_div_iff₀ (by positivity : 0 < (2*Real.pi*|ξ|)^N)).mpr
  simpa only [mul_comm] using pairMeanFourier_power_bound f N hf hc ξ

theorem fourierDecay_iteratedDeriv_ofReal (ω : ℝ → ℝ) (N : ℕ) (hω : ContDiff ℝ N ω) :
    iteratedDeriv N (fun u => (ω u:ℂ)) = fun u => ((iteratedDeriv N ω u:ℝ):ℂ) := by
  funext u
  have he := Complex.ofRealCLM.iteratedFDeriv_comp_left (hω.contDiffAt (x := u)) (i := N) le_rfl
  exact congrArg (fun g => g (fun _ : Fin N => (1:ℝ))) he

theorem fourierDecay_ofReal_compact (ω : ℝ → ℝ) (hc : HasCompactSupport ω) :
    HasCompactSupport (fun u => (ω u:ℂ)) := by
  exact hc.comp_left (g := Complex.ofReal) (by simp)

theorem fourierDerivativeL1_nonneg (ω : ℝ → ℝ) (N : ℕ) : 0 ≤ fourierDerivativeL1 ω N :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem fourierDerivativeL1_zero_order (ω : ℝ → ℝ) : fourierDerivativeL1 ω 0 = ∫ u : ℝ, |ω u| := by
  simp [fourierDerivativeL1]

theorem fourierDecay_real_power_bound (ω : ℝ → ℝ) (N : ℕ)
    (hω : ContDiff ℝ N ω) (hc : HasCompactSupport ω) (ξ : ℝ) :
    (2*Real.pi*|ξ|)^N * ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤ fourierDerivativeL1 ω N := by
  have he := pairMeanFourier_power_bound (fun u => (ω u:ℂ)) N
    (Complex.ofRealCLM.contDiff.comp hω) (fourierDecay_ofReal_compact ω hc) ξ
  simpa only [fourierDecay_iteratedDeriv_ofReal ω N hω,Complex.norm_real,Real.norm_eq_abs,
    fourierDerivativeL1] using he

theorem fourierDecay_real_bound (ω : ℝ → ℝ) (N : ℕ)
    (hω : ContDiff ℝ N ω) (hc : HasCompactSupport ω) (ξ : ℝ) (hξ : ξ≠0) :
    ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤ fourierDerivativeL1 ω N/(2*Real.pi*|ξ|)^N := by
  apply (le_div_iff₀ (by positivity : 0 < (2*Real.pi*|ξ|)^N)).mpr
  simpa only [mul_comm] using fourierDecay_real_power_bound ω N hω hc ξ

theorem fourierDecay_real_mass (ω : ℝ → ℝ) (ξ : ℝ) :
    ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤ fourierDerivativeL1 ω 0 := by
  simpa only [fourierDerivativeL1_zero_order,Complex.norm_real,Real.norm_eq_abs] using
    pairMeanFourier_norm_bound (fun u => (ω u:ℂ)) ξ

theorem fourierDecay_real_min (ω : ℝ → ℝ) (N : ℕ)
    (hω : ContDiff ℝ N ω) (hc : HasCompactSupport ω) (ξ : ℝ) (hξ : ξ≠0) :
    ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤
      min (fourierDerivativeL1 ω 0) (fourierDerivativeL1 ω N/(2*Real.pi*|ξ|)^N) :=
  le_min (fourierDecay_real_mass ω ξ) (fourierDecay_real_bound ω N hω hc ξ hξ)

/-- Uniformity uses explicit derivative-norm bounds, with no family compactness premise. -/
theorem fourierDecay_real_uniform (ω : ℝ → ℝ) (N : ℕ)
    (hω : ContDiff ℝ N ω) (hc : HasCompactSupport ω) (D₀ Dₙ : ℝ)
    (h0 : fourierDerivativeL1 ω 0 ≤ D₀) (hn : fourierDerivativeL1 ω N ≤ Dₙ)
    (ξ : ℝ) (hξ : ξ≠0) :
    ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤ min D₀ (Dₙ/(2*Real.pi*|ξ|)^N) :=
  le_min ((fourierDecay_real_mass ω ξ).trans h0)
    ((fourierDecay_real_bound ω N hω hc ξ hξ).trans
      (div_le_div_of_nonneg_right hn (by positivity)))

theorem fourierDecay_zero_frequency (ω : ℝ → ℝ) :
    pairMeanFourier (fun u => (ω u:ℂ)) 0 = ∫ u : ℝ, (ω u:ℂ) :=
  pairMeanFourier_zero _

theorem fourierDecay_first_order (ω : ℝ → ℝ) (hω : ContDiff ℝ 1 ω)
    (hc : HasCompactSupport ω) (ξ : ℝ) (hξ : ξ≠0) :
    ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤ (∫ u : ℝ, |deriv ω u|)/(2*Real.pi*|ξ|) := by
  simpa only [fourierDerivativeL1,iteratedDeriv_one,pow_one] using
    fourierDecay_real_bound ω 1 hω hc ξ hξ

theorem fourierDerivativeL1_zero_weight (N : ℕ) : fourierDerivativeL1 (fun _ => 0) N = 0 := by
  simp [fourierDerivativeL1,iteratedDeriv_fun_const_zero]

theorem fourierDerivativeL1_neg_weight (ω : ℝ → ℝ) (N : ℕ) :
    fourierDerivativeL1 (fun u => -ω u) N = fourierDerivativeL1 ω N := by
  simp only [fourierDerivativeL1,iteratedDeriv_fun_neg,abs_neg]

theorem fourierDecay_real_neg_weight (ω : ℝ → ℝ) (ξ : ℝ) :
    ‖pairMeanFourier (fun u => (-ω u:ℂ)) ξ‖ = ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ := by
  simp [pairMeanFourier,integral_neg]

/-- At order zero even the origin has denominator one, following 0^0=1. -/
theorem fourierDecay_order_zero (ω : ℝ → ℝ) (ξ : ℝ) :
    (2*Real.pi*|ξ|)^0 * ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤ fourierDerivativeL1 ω 0 := by
  simpa using fourierDecay_real_mass ω ξ

theorem fourierDecay_unit_frequencies (ω : ℝ → ℝ) (N : ℕ)
    (hω : ContDiff ℝ N ω) (hc : HasCompactSupport ω) :
    (‖pairMeanFourier (fun u => (ω u:ℂ)) 1‖ ≤
      min (fourierDerivativeL1 ω 0) (fourierDerivativeL1 ω N/(2*Real.pi)^N)) ∧
    (‖pairMeanFourier (fun u => (ω u:ℂ)) (-1)‖ ≤
      min (fourierDerivativeL1 ω 0) (fourierDerivativeL1 ω N/(2*Real.pi)^N)) := by
  constructor
  · simpa using fourierDecay_real_min ω N hω hc 1 (by norm_num)
  · simpa using fourierDecay_real_min ω N hω hc (-1) (by norm_num)

end
end HigherCorrelations
