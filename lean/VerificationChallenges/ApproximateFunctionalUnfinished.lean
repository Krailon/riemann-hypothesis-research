import HigherCorrelations.ApproximateFunctionalDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.CircleIntegral

-- Definition-only expected statements; unfinished solutions must be rejected.
namespace HigherCorrelations
noncomputable section
open Complex Set MeasureTheory Filter Asymptotics
open scoped ComplexConjugate Topology

theorem afePoint_re (σ t : ℝ) : (afePoint σ t).re = σ := by sorry

theorem afePoint_im (σ t : ℝ) : (afePoint σ t).im = t := by sorry

theorem afePoint_reflect (σ t : ℝ) : 1-afePoint σ t = afePoint (1-σ) (-t) := by sorry

theorem afePoint_conj (σ t : ℝ) : conj (afePoint σ t) = afePoint σ (-t) := by sorry

theorem afePolynomial_nat (s : ℂ) (N : ℕ) :
    afePolynomial s N = ∑ n ∈ Finset.Icc 1 N, (n : ℂ)^(-s) := by sorry

theorem afePolynomial_one (s : ℂ) : afePolynomial s 1 = 1 := by sorry

theorem afePolynomial_lt_one (s : ℂ) {x : ℝ} (hx : x < 1) :
    afePolynomial s x = 0 := by sorry

theorem afePolynomial_conj (s : ℂ) (x : ℝ) :
    afePolynomial (conj s) x = conj (afePolynomial s x) := by sorry

theorem afe_identity (s : ℂ) (x y : ℝ) :
    riemannZeta s = afePolynomial s x + pairChi s * afePolynomial (1-s) y +
      afeRemainder s x y := by sorry

theorem afe_phase_identity (σ t x y : ℝ) :
    riemannZeta (afePoint σ t) = afePolynomial (afePoint σ t) x +
      afePhase σ t * afePolynomial (1-afePoint σ t) y +
      afePhaseRemainder σ t x y := by sorry

theorem afe_phase_remainder_split (σ t x y : ℝ) :
    afePhaseRemainder σ t x y = afeRemainder (afePoint σ t) x y +
      (pairChi (afePoint σ t)-afePhase σ t) * afePolynomial (1-afePoint σ t) y := by sorry

theorem afe_phase_remainder_bound (σ t x y : ℝ) :
    ‖afePhaseRemainder σ t x y‖ ≤ ‖afeRemainder (afePoint σ t) x y‖ +
      ‖pairChi (afePoint σ t)-afePhase σ t‖ * ‖afePolynomial (1-afePoint σ t) y‖ := by sorry

theorem afeChi_functional_eq (s : ℂ) (hs : s.im ≠ 0) :
    riemannZeta s = pairChi s * riemannZeta (1-s) := by sorry

theorem afeChi_conj (s : ℂ) : pairChi (conj s) = conj (pairChi s) := by sorry

theorem afeRemainder_conj (s : ℂ) (x y : ℝ) :
    afeRemainder (conj s) x y = conj (afeRemainder s x y) := by sorry

theorem afeChi_reflection (s : ℂ) (hs : s.im ≠ 0) : pairChi s * pairChi (1-s) = 1 := by sorry

theorem afeRemainder_reflection (s : ℂ) (hs : s.im ≠ 0) (x y : ℝ) :
    afeRemainder s y x = pairChi s * afeRemainder (1-s) x y := by sorry

theorem afeRemainder_reflection_norm (s : ℂ) (hs : s.im ≠ 0) (x y : ℝ) :
    ‖afeRemainder s y x‖ = ‖pairChi s‖ * ‖afeRemainder (1-s) x y‖ := by sorry

theorem afeChi_critical_norm {t : ℝ} (ht : t ≠ 0) : ‖pairChi (afePoint (1/2) t)‖ = 1 := by sorry

theorem afeHeight_nonneg (t : ℝ) : 0 ≤ afeHeight t := by sorry

theorem afeHeight_pos {t : ℝ} (ht : t ≠ 0) : 0 < afeHeight t := by sorry

theorem afeHeight_neg (t : ℝ) : afeHeight (-t) = afeHeight t := by sorry

theorem afeHeight_ge_one {t : ℝ} (ht : 2*Real.pi ≤ |t|) : 1 ≤ afeHeight t := by sorry

theorem afePhase_norm (σ t : ℝ) : ‖afePhase σ t‖ = afeHeight t ^ (1/2-σ) := by sorry

theorem afePhase_ne_zero (σ : ℝ) {t : ℝ} (ht : t ≠ 0) : afePhase σ t ≠ 0 := by sorry

theorem afePhase_conj (σ t : ℝ) : afePhase σ (-t) = conj (afePhase σ t) := by sorry

theorem afePhase_positive (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    afePhase σ t = (afeHeight t ^ (1/2-σ) : ℝ) *
      exp (((-t * Real.log (afeHeight t / Real.exp 1) + Real.pi/4 : ℝ) : ℂ)*I) := by sorry

theorem afePhase_critical_norm (t : ℝ) : ‖afePhase (1/2) t‖ = 1 := by sorry

theorem afePhase_mul_conj (σ t : ℝ) :
    afePhase σ t * afePhase σ (-t) = (afeHeight t ^ (1-2*σ) : ℝ) := by sorry

theorem afePolynomial_norm_le_sum (s : ℂ) (x : ℝ) :
    ‖afePolynomial s x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)^(-s.re) := by sorry

theorem afePolynomial_norm_le_floor (s : ℂ) (hs : 0 ≤ s.re) (x : ℝ) :
    ‖afePolynomial s x‖ ≤ ⌊x⌋₊ := by sorry

theorem afePolynomial_norm_le (s : ℂ) (hs : 0 ≤ s.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖afePolynomial s x‖ ≤ x := by sorry

theorem afePolynomial_step (s : ℂ) (N : ℕ) :
    afePolynomial s (N+1 : ℕ) = afePolynomial s N + (N+1 : ℂ)^(-s) := by sorry

theorem afeTwist_admissible (μ₁ μ₂ T t : ℝ)
    (hμ : 1 ≤ μ₁) (horder : μ₁ ≤ μ₂) (hmax : μ₂ ≤ T/(2*Real.pi))
    (ht : T ≤ t) :
    1 ≤ afeTwistShort μ₁ μ₂ t ∧
    afeTwistShort μ₁ μ₂ t ≤ afeTwistLong μ₁ μ₂ t ∧
    2*Real.pi * afeTwistShort μ₁ μ₂ t * afeTwistLong μ₁ μ₂ t = t := by sorry

theorem afeTwist_short_continuous (μ₁ μ₂ : ℝ) : Continuous (afeTwistShort μ₁ μ₂) := by sorry

theorem afeTwist_long_continuous (μ₁ μ₂ : ℝ) : Continuous (afeTwistLong μ₁ μ₂) := by sorry

theorem afePolynomial_continuous (x : ℝ) : Continuous (fun s : ℂ => afePolynomial s x) := by sorry

theorem afePolynomial_measurable {s : ℝ → ℂ} {x : ℝ → ℝ}
    (hs : Measurable s) (hx : Measurable x) :
    Measurable (fun t => afePolynomial (s t) (x t)) := by sorry

theorem afePolynomial_integrableOn {s : ℝ → ℂ} {x : ℝ → ℝ} (a b B : ℝ)
    (hs : Measurable s) (hx : Measurable x)
    (hσ : ∀ t ∈ Icc a b, 0 ≤ (s t).re)
    (hbound : ∀ t ∈ Icc a b, 0 ≤ x t ∧ x t ≤ B) :
    IntegrableOn (fun t => afePolynomial (s t) (x t)) (Icc a b) := by sorry

theorem afePolynomial_continuousCutoff_integrable (σ ε a b : ℝ) (hσ : 0 ≤ σ)
    (x : ℝ → ℝ) (hx : Continuous x) (hx₀ : ∀ t, 0 ≤ x t) :
    IntegrableOn (fun t => afePolynomial (afePoint σ (ε*t)) (x t)) (Icc a b) := by sorry

theorem afeTwist_four_polynomials_integrable (σ μ₁ μ₂ a b : ℝ)
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) :
    IntegrableOn (fun t => afePolynomial (afePoint σ t) (afeTwistShort μ₁ μ₂ t)) (Icc a b) ∧
    IntegrableOn (fun t => afePolynomial (1-afePoint σ t) (afeTwistLong μ₁ μ₂ t)) (Icc a b) ∧
    IntegrableOn (fun t => afePolynomial (afePoint σ (-t)) (afeTwistLong μ₁ μ₂ t)) (Icc a b) ∧
    IntegrableOn (fun t => afePolynomial (1-afePoint σ (-t)) (afeTwistShort μ₁ μ₂ t)) (Icc a b) := by sorry

theorem afeChi_continuousAt (s : ℂ) (hs : s.im ≠ 0) : ContinuousAt pairChi s := by sorry

theorem afeZetaChi_compact_bound (δ H : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → δ ≤ |t| → |t| ≤ H →
      ‖riemannZeta (afePoint σ t)‖ + ‖pairChi (afePoint σ t)‖ ≤ B := by sorry

theorem afeRemainder_bounded_height (δ H X : ℝ) (hδ : 0 < δ) (hX : 0 ≤ X) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ t x y : ℝ,
      0 ≤ σ → σ ≤ 1 → δ ≤ |t| → |t| ≤ H →
      0 ≤ x → x ≤ X → 0 ≤ y → y ≤ X → ‖afeRemainder (afePoint σ t) x y‖ ≤ B := by sorry

theorem afeRemainder_compact_short (H : ℝ) (hH : 2*Real.pi ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t x y : ℝ,
      0 ≤ σ → σ ≤ 1 → 2*Real.pi ≤ |t| → |t| ≤ H →
      1 ≤ x → 1 ≤ y → 2*Real.pi*x*y = |t| →
      ‖afeRemainder (afePoint σ t) x y‖ ≤ C*x^(-σ) := by sorry

theorem afe_exp_near_lattice (z : ℂ) (hz : ‖exp z-1‖ ≤ 1/2) :
    ∃ n : ℤ, ‖z - n*(2*(Real.pi:ℂ)*I)‖ ≤ (3/2)*‖exp z-1‖ := by sorry

theorem afe_exp_sub_one_lower (z : ℂ) (r : ℝ)
    (hsep : ∀ n : ℤ, r ≤ ‖z-n*(2*(Real.pi:ℂ)*I)‖) :
    min (1/2 : ℝ) (2*r/3) ≤ ‖exp z-1‖ := by sorry

theorem afe_contour_denominator (z : ℂ)
    (hsep : ∀ n : ℤ, (1/4 : ℝ) ≤ ‖z-n*(2*(Real.pi:ℂ)*I)‖) :
    1/6 ≤ ‖exp z-1‖ := by sorry

theorem afe_contour_inverse_bound (z : ℂ)
    (hsep : ∀ n : ℤ, (1/4 : ℝ) ≤ ‖z-n*(2*(Real.pi:ℂ)*I)‖) :
    ‖(exp z-1)⁻¹‖ ≤ 6 := by sorry

theorem afe_floor_ratio {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ ⌊x⌋₊ ∧ x ≤ 2*(⌊x⌋₊ : ℝ) := by sorry

theorem afe_contour_parameters (σ τ x y : ℝ)
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (hτ : 2*Real.pi ≤ τ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : 2*Real.pi*x*y = τ) :
    (0:ℝ) < 1/4 ∧ 1/4 ≤ Real.pi/Real.sqrt 2 ∧
    (1/4)*x/τ ≤ 1/4 ∧
    (1/4:ℝ) ≤ 3*Real.sqrt 2/(10+4*(1-σ)/(2*Real.pi)) ∧
    (1/4:ℝ) ≤ (1/4)*τ/x ∧
    Real.pi*x/(2*(⌊x⌋₊ : ℝ)) ≤ 4 := by sorry

theorem afeStirlingStep_bound (z : ℂ) (hz : 2 ≤ ‖z‖) :
    ‖afeStirlingStep z‖ ≤ 2 / ‖z‖^2 := by sorry

theorem afeStirlingMain_increment_closed (z : ℂ) (hz : 0 ≤ z.re) (hn : z ≠ 0) :
    afeStirlingMain (z+1)-afeStirlingMain z = log z + afeStirlingStep z := by sorry

theorem afeStirlingMain_increment (z : ℂ) (hz : 0 < z.re) :
    afeStirlingMain (z+1)-afeStirlingMain z = log z + afeStirlingStep z := by sorry

theorem afe_shift_norm (z : ℂ) (hz : 0 ≤ z.re) (u : ℝ) (hu : 0 ≤ u) :
    ‖z‖ ≤ ‖z+u‖ ∧ (‖z‖+u)^2 ≤ 2*‖z+u‖^2 := by sorry

theorem afeStirlingStep_shift_bound (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) (n : ℕ) :
    ‖afeStirlingStep (z+n)‖ ≤ 8*((‖z‖+(n:ℝ))⁻¹-(‖z‖+(n:ℝ)+1)⁻¹) := by sorry

theorem afe_inverse_differences_hasSum (a : ℝ) (ha : 0 < a) :
    HasSum (fun n : ℕ => (a+(n:ℝ))⁻¹-(a+(n:ℝ)+1)⁻¹) a⁻¹ := by sorry

theorem afeStirlingStep_summable_norm (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) :
    Summable (fun n : ℕ => ‖afeStirlingStep (z+n)‖) := by sorry

theorem afeStirlingCorrection_bound (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) :
    ‖afeStirlingCorrection z‖ ≤ 8/‖z‖ := by sorry

theorem afeStirlingCorrection_tail (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) (N : ℕ) :
    ‖afeStirlingCorrection z - ∑ n ∈ Finset.range N, afeStirlingStep (z+n)‖ ≤
      8/‖z+N‖ := by sorry

theorem afeStirlingCorrection_succ (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) :
    afeStirlingCorrection z = afeStirlingStep z + afeStirlingCorrection (z+1) := by sorry

theorem afeStirling_finite_logs (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ∑ n ∈ Finset.range N, log (z+n) = afeStirlingMain (z+N)-afeStirlingMain z -
      ∑ n ∈ Finset.range N, afeStirlingStep (z+n) := by sorry

theorem afe_logGammaSeq_decomposition (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    logGammaSeq z N = afeStirlingMain z +
      (z*(Real.log N:ℂ)+(Real.log (N.factorial):ℂ)-afeStirlingMain (z+N+1)) +
      ∑ n ∈ Finset.range (N+1), afeStirlingStep (z+n) := by sorry

theorem afe_scaled_log_limit (v : ℂ) :
    Tendsto (fun n : ℕ => (n+1:ℂ)*log (1+v/(n+1:ℂ))) atTop (𝓝 v) := by sorry

theorem afe_small_log_limit (v : ℂ) :
    Tendsto (fun n : ℕ => log (1+v/(n+1:ℂ))) atTop (𝓝 (0:ℂ)) := by sorry

theorem afeStirling_offset_limit (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => z*(Real.log (n+1:ℝ):ℂ) +
      (Real.log ((n+1).factorial):ℂ) - afeStirlingMain (z+(n+1:ℕ)+1))
      atTop (𝓝 ((Real.log (2*Real.pi)/2:ℝ):ℂ)) := by sorry

theorem afe_logGammaSeq_limit (z : ℂ) (hz : 0 < z.re) (hnorm : 2 ≤ ‖z‖) :
    Tendsto (fun n : ℕ => logGammaSeq z (n+1)) atTop
      (𝓝 (afeStirlingMain z + ((Real.log (2*Real.pi)/2:ℝ):ℂ) + afeStirlingCorrection z)) := by sorry

theorem afeGamma_stirling_identity (z : ℂ) (hz : 0 < z.re) (hnorm : 2 ≤ ‖z‖) :
    Gamma z = exp (afeStirlingMain z + ((Real.log (2*Real.pi)/2:ℝ):ℂ) +
      afeStirlingCorrection z) := by sorry

theorem afeGamma_stirling_closed (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) :
    Gamma z = exp (afeStirlingMain z + ((Real.log (2*Real.pi)/2:ℝ):ℂ) +
      afeStirlingCorrection z) := by sorry

theorem afeGamma_stirling_relative (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 8 ≤ ‖z‖) :
    ‖Gamma z / exp (afeStirlingMain z + ((Real.log (2*Real.pi)/2:ℝ):ℂ)) - 1‖ ≤
      16/‖z‖ := by sorry

theorem afeGammaVerticalError_bound (a t : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1/2) (ht : 2 ≤ t) :
    ‖afeGammaVerticalError a t‖ ≤ 9/t := by sorry

theorem afe_log_lower_vertical (a t : ℝ) (ht : 0 < t) :
    log ((a:ℂ)-t*I) = (Real.log t:ℂ) - (Real.pi:ℂ)/2*I +
      log (1+(a/t:ℝ)*I) := by sorry

theorem afe_sin_factor (z : ℂ) :
    sin z = exp ((Real.pi:ℂ)/2*I-(Real.log 2:ℂ)) *
      exp (-z*I) * (1-exp (2*z*I)) := by sorry

theorem afePhase_exp_positive (σ t : ℝ) (ht : 0 < t) :
    afePhase σ t = exp ((((1/2-σ)*Real.log (afeHeight t):ℝ):ℂ) +
      ((-t*Real.log (afeHeight t / Real.exp 1)+Real.pi/4:ℝ):ℂ)*I) := by sorry

theorem afeChi_phase_factor (σ t : ℝ) (hσ : σ ≤ 1) (ht : 2 ≤ t) :
    pairChi (afePoint σ t) = afePhase σ t * exp (afeGammaVerticalError (1-σ) t) *
      (1-exp ((Real.pi:ℂ)*afePoint σ t*I)) := by sorry

theorem afeChi_phase_high (σ t : ℝ) (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (ht : 18 ≤ t) :
    ‖pairChi (afePoint σ t)-afePhase σ t‖ ≤ 20*afeHeight t^(1/2-σ)/t := by sorry

theorem afeChi_phase_uniform_positive :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2*Real.pi ≤ t →
      ‖pairChi (afePoint σ t)-afePhase σ t‖ ≤ C*afeHeight t^(1/2-σ)/t := by sorry

theorem afeChi_phase_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2*Real.pi ≤ |t| →
      ‖pairChi (afePoint σ t)-afePhase σ t‖ ≤ C*afeHeight t^(1/2-σ)/|t| := by sorry

theorem afe_phase_replacement_identity (σ t x y : ℝ) :
    afePhaseRemainder σ t x y - afeRemainder (afePoint σ t) x y =
      (pairChi (afePoint σ t)-afePhase σ t)*afePolynomial (1-afePoint σ t) y := by sorry

theorem afe_phase_replacement_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t x y : ℝ,
      1/2 ≤ σ → σ ≤ 1 → 2*Real.pi ≤ |t| → 1 ≤ x → x ≤ y →
      2*Real.pi*x*y = |t| →
      ‖afePhaseRemainder σ t x y-afeRemainder (afePoint σ t) x y‖ ≤ C*x^(-σ) ∧
      ‖afePhaseRemainder σ t y x-afeRemainder (afePoint σ t) y x‖ ≤
        C*afeHeight t^(1/2-σ)*x^(σ-1) := by sorry

theorem afe_laplace_term (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ))) =
      (1/(n+1:ℂ)^s)*Gamma s := by sorry

theorem afe_laplace_integrable (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun u : ℝ => (u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ))) (Ioi 0) := by sorry

theorem afe_laplace_integral_norm (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    (∫ u : ℝ in Ioi 0, ‖(u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ))‖) =
      (n+1:ℝ)^(-s.re)*Real.Gamma s.re := by sorry

theorem afe_laplace_summable_integral_norm (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ u : ℝ in Ioi 0,
      ‖(u:ℂ)^(s-1)*exp (-((n+1:ℝ)*u:ℝ))‖) := by sorry

theorem afe_exponential_series (u : ℝ) (hu : 0 < u) :
    (∑' n : ℕ, exp (-((n+1:ℝ)*u:ℝ))) = 1/(exp (u:ℂ)-1) := by sorry

theorem afe_zeta_mellin (s : ℂ) (hs : 1 < s.re) :
    (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)/(exp (u:ℂ)-1)) = Gamma s * riemannZeta s := by sorry

theorem afePolynomial_nat_succ (s : ℂ) (m : ℕ) :
    afePolynomial s (m+1:ℕ) = afePolynomial s m + 1/(m+1:ℂ)^s := by sorry

theorem afePolynomial_range (s : ℂ) (m : ℕ) :
    afePolynomial s m = ∑ n ∈ Finset.range m, 1/(n+1:ℂ)^s := by sorry

theorem afe_dirichlet_tail (s : ℂ) (hs : 1 < s.re) (m : ℕ) :
    (∑' n : ℕ, 1/((n+m:ℕ)+1:ℂ)^s) = riemannZeta s - afePolynomial s m := by sorry

theorem afe_exponential_tail (u : ℝ) (hu : 0 < u) (m : ℕ) :
    (∑' n : ℕ, exp (-(((n+m:ℕ)+1:ℝ)*u:ℝ))) =
      exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by sorry

theorem afe_mellin_tail (s : ℂ) (hs : 1 < s.re) (m : ℕ) :
    (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) =
      Gamma s * (riemannZeta s - afePolynomial s m) := by sorry

theorem afe_zeta_mellin_integrable (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => (u:ℂ)^(s-1)/(exp (u:ℂ)-1)) (Ioi 0) := by sorry

theorem afe_mellin_tail_integrable (s : ℂ) (hs : 1 < s.re) (m : ℕ) :
    IntegrableOn (fun u : ℝ =>
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) (Ioi 0) := by sorry

theorem afeHankelLog_exp (z : ℂ) (hz : z ≠ 0) :
    exp (afeHankelLog z) = z := by sorry

theorem afeHankelLog_derivative (z : ℂ) (hz : -z ∈ slitPlane) :
    HasDerivAt afeHankelLog z⁻¹ z := by sorry

theorem afeHankelLog_upper_pole (a : ℝ) (ha : 0 < a) :
    afeHankelLog ((a:ℂ)*I) = (Real.log a:ℂ) + (Real.pi:ℂ)/2*I := by sorry

theorem afeHankelLog_lower_pole (a : ℝ) (ha : 0 < a) :
    afeHankelLog (-((a:ℂ)*I)) = (Real.log a:ℂ) + 3*(Real.pi:ℂ)/2*I := by sorry

theorem afeHankelPower_upper_pole (s : ℂ) (a : ℝ) (ha : 0 < a) :
    afeHankelPower s ((a:ℂ)*I) =
      (a:ℂ)^(s-1)*exp ((s-1)*(Real.pi:ℂ)/2*I) := by sorry

theorem afeHankelPower_lower_pole (s : ℂ) (a : ℝ) (ha : 0 < a) :
    afeHankelPower s (-((a:ℂ)*I)) =
      (a:ℂ)^(s-1)*exp ((s-1)*3*(Real.pi:ℂ)/2*I) := by sorry

theorem afe_exp_sine_jump (z : ℂ) :
    exp (2*z*I)-1 = 2*I*exp (z*I)*sin z := by sorry

theorem afeHankelPrefactor_jump (s : ℂ) (hs : s.im ≠ 0) :
    afeHankelPrefactor s * (exp (2*(Real.pi:ℂ)*s*I)-1) * Gamma s = 1 := by sorry

theorem afeHankelPower_norm (s z : ℂ) (hz : z ≠ 0) :
    ‖afeHankelPower s z‖ = ‖z‖^(s.re-1) *
      Real.exp (-s.im*(arg (-z)+Real.pi)) := by sorry

theorem afeHankelPower_derivative (s z : ℂ) (hz : -z ∈ slitPlane) :
    HasDerivAt (afeHankelPower s) ((s-1)*z⁻¹*afeHankelPower s z) z := by sorry

theorem afeHankelKernel_residue (s : ℂ) (m : ℕ) (p : ℂ)
    (hp : -p ∈ slitPlane) (he : exp p = 1) :
    residue (afeHankelKernel s m) p = afeHankelPower s p := by sorry

theorem afeHankelPrefactor_mellin (s : ℂ) (hs : 1 < s.re) (ht : s.im ≠ 0) (m : ℕ) :
    afeHankelPrefactor s * (exp (2*(Real.pi:ℂ)*s*I)-1) *
      (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) =
      riemannZeta s - afePolynomial s m := by sorry

theorem afeHankelPower_pole_pair (s : ℂ) (a : ℝ) (ha : 0 < a) :
    afeHankelPower s ((a:ℂ)*I) + afeHankelPower s (-((a:ℂ)*I)) =
      -2 * exp ((Real.pi:ℂ)*s*I) * sin ((Real.pi:ℂ)*s/2) * (a:ℂ)^(s-1) := by sorry

theorem afeChi_power (s : ℂ) :
    pairChi s = 2*(2*(Real.pi:ℂ))^(s-1)*sin ((Real.pi:ℂ)*s/2)*Gamma (1-s) := by sorry

theorem afeHankelKernel_residue_pair (s : ℂ) (m k : ℕ) (hk : 0 < k) :
    afeHankelPrefactor s * (2*(Real.pi:ℂ)*I) *
      (residue (afeHankelKernel s m) ((2*Real.pi*k:ℝ)*I) +
       residue (afeHankelKernel s m) (-((2*Real.pi*k:ℝ)*I))) =
      -pairChi s * (k:ℂ)^(s-1) := by sorry

theorem afe_exp_small_denominator (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    ‖z‖/2 ≤ ‖exp z-1‖ := by sorry

theorem afeHankelPower_bound (s z : ℂ) (hz : z ≠ 0) :
    ‖afeHankelPower s z‖ ≤ ‖z‖^(s.re-1)*Real.exp (2*Real.pi*|s.im|) := by sorry

theorem afeHankelKernel_small_bound (s : ℂ) (m : ℕ) (z : ℂ)
    (hz : z ≠ 0) (hr : ‖z‖ ≤ 1/2) :
    ‖afeHankelKernel s m z‖ ≤
      2*‖z‖^(s.re-1)/‖z‖*Real.exp (2*Real.pi*|s.im|+(m:ℝ)/2) := by sorry

theorem afeHankelKernel_measurable (s : ℂ) (m : ℕ) :
    Measurable (afeHankelKernel s m) := by sorry

theorem afeHankel_circle_bound (s : ℂ) (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    ‖∮ z in C(0,r), afeHankelKernel s m z‖ ≤
      4*Real.pi*r^(s.re-1)*Real.exp (2*Real.pi*|s.im|+(m:ℝ)/2) := by sorry

theorem afeHankel_circle_integrable (s : ℂ) (m : ℕ) (r : ℝ)
    (hr : 0 < r) (hr' : r ≤ 1/2) :
    CircleIntegrable (afeHankelKernel s m) 0 r := by sorry

theorem afeHankel_circle_tendsto_zero (s : ℂ) (hs : 1 < s.re) (m : ℕ) :
    Tendsto (fun r : ℝ => ∮ z in C(0,r), afeHankelKernel s m z) (𝓝[>] 0) (𝓝 0) := by sorry

theorem afeHankelLog_circle (r θ : ℝ) (hr : 0 < r)
    (hθ : 0 < θ) (hθ' : θ ≤ 2*Real.pi) :
    afeHankelLog (circleMap 0 r θ) = (Real.log r:ℂ)+(θ:ℂ)*I := by sorry

theorem afeHankel_circle_lift (s : ℂ) (m : ℕ) (r : ℝ) (hr : 0 < r) :
    (∮ z in C(0,r), afeHankelKernel s m z) =
      I * ∫ θ : ℝ in 0..2*Real.pi, afeHankelLift s m ((Real.log r:ℂ)+(θ:ℂ)*I) := by sorry

theorem afeHankelLift_differentiable (s : ℂ) (m : ℕ) (w : ℂ)
    (hw : Real.exp w.re ≤ 1/2) :
    DifferentiableAt ℂ (afeHankelLift s m) w := by sorry

theorem afeHankelLift_period (s w : ℂ) (m : ℕ) :
    afeHankelLift s m (w+2*(Real.pi:ℂ)*I) =
      exp (2*(Real.pi:ℂ)*s*I)*afeHankelLift s m w := by sorry

theorem afeHankelLift_rectangle (s : ℂ) (m : ℕ) (a b : ℝ)
    (hab : a ≤ b) (hb : Real.exp b ≤ 1/2) :
    RectangleIntegral (afeHankelLift s m) (a:ℂ) ((b:ℂ)+2*(Real.pi:ℂ)*I) = 0 := by sorry

theorem afe_mellin_kernel_continuous (s : ℂ) (m : ℕ) :
    ContinuousOn (fun u : ℝ =>
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) (Ioi 0) := by sorry

theorem afeHankelLift_real_integral (s : ℂ) (m : ℕ) (a b : ℝ) :
    (∫ v : ℝ in a..b, afeHankelLift s m (v:ℂ)) =
      ∫ u : ℝ in Real.exp a..Real.exp b,
        (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by sorry

theorem afeHankel_circle_difference (s : ℂ) (m : ℕ) (r R : ℝ)
    (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/2) :
    (∮ z in C(0,R), afeHankelKernel s m z) -
      (∮ z in C(0,r), afeHankelKernel s m z) =
      (exp (2*(Real.pi:ℂ)*s*I)-1) *
        ∫ u : ℝ in r..R, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by sorry

theorem afeHankel_circle_mellin (s : ℂ) (hs : 1 < s.re) (m : ℕ)
    (R : ℝ) (hR : 0 < R) (hR' : R ≤ 1/2) :
    (∮ z in C(0,R), afeHankelKernel s m z) =
      (exp (2*(Real.pi:ℂ)*s*I)-1) *
        ∫ u : ℝ in 0..R, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by sorry

theorem afeHankel_initial_identity (s : ℂ) (hs : 1 < s.re) (ht : s.im ≠ 0)
    (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    riemannZeta s - afePolynomial s m =
      afeHankelPrefactor s * ((∮ z in C(0,r), afeHankelKernel s m z) +
        (exp (2*(Real.pi:ℂ)*s*I)-1) *
          ∫ u : ℝ in Ioi r,
            (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by sorry

theorem afe_mellin_kernel_norm (s : ℂ) (m : ℕ) (u : ℝ) (hu : 0 < u) :
    ‖(u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)‖ =
      u^(s.re-1)*Real.exp (-((m:ℝ)*u))/(Real.exp u-1) := by sorry

theorem afe_mellin_ray_majorant (s : ℂ) (m : ℕ) (r a u : ℝ)
    (hr : 0 < r) (hu : r ≤ u) (ha : s.re ≤ a) :
    ‖(u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)‖ ≤
      r^(s.re-a) *
        ‖(u:ℂ)^((a:ℂ)-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)‖ := by sorry

theorem afe_mellin_ray_integrable (s : ℂ) (m : ℕ) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun u : ℝ =>
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) (Ioi r) := by sorry

theorem afeHankelRayWeight_integrable (m : ℕ) (r : ℝ) (hr : 0 < r) :
    Integrable (afeHankelRayWeight m r) := by sorry

theorem afeHankelRayWeight_decay (m : ℕ) (r : ℝ) :
    afeHankelRayWeight m r =O[atTop] (fun u : ℝ => Real.exp (-u)) := by sorry

theorem afeHankelRayWeight_zero_bound (m : ℕ) (r b : ℝ) (hr : 0 < r) :
    afeHankelRayWeight m r =O[𝓝[>] 0] (fun u : ℝ => u^(-b)) := by sorry

theorem afeHankelRayWeight_mellin (s : ℂ) (m : ℕ) (r : ℝ) (hr : 0 < r) :
    mellin (afeHankelRayWeight m r) s =
      ∫ u : ℝ in Ioi r, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by sorry

theorem afeHankel_ray_differentiable (m : ℕ) (r : ℝ) (hr : 0 < r) :
    Differentiable ℂ (fun s : ℂ => ∫ u : ℝ in Ioi r,
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by sorry

theorem afe_compact_exp_integral_entire (w A : ℝ → ℂ) (hw : Continuous w)
    (hA : Continuous A) (a b : ℝ) :
    Differentiable ℂ (fun s : ℂ => ∫ θ : ℝ in a..b, A θ * exp (s*w θ)) := by sorry

theorem afeHankel_circle_differentiable (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    Differentiable ℂ (fun s : ℂ => ∮ z in C(0,r), afeHankelKernel s m z) := by sorry

theorem afePolynomial_differentiable (x : ℝ) :
    Differentiable ℂ (fun s : ℂ => afePolynomial s x) := by sorry

theorem afeHankelPrefactor_differentiable (s : ℂ) (hs : s.im ≠ 0) :
    DifferentiableAt ℂ afeHankelPrefactor s := by sorry

theorem afeHankel_initial_identity_on (U : Set ℂ) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hnonreal : ∀ s ∈ U, s.im ≠ 0)
    (a : ℂ) (ha : a ∈ U) (ha' : 1 < a.re)
    (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    ∀ s ∈ U, riemannZeta s - afePolynomial s m =
      afeHankelPrefactor s * ((∮ z in C(0,r), afeHankelKernel s m z) +
        (exp (2*(Real.pi:ℂ)*s*I)-1) *
          ∫ u : ℝ in Ioi r,
            (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by sorry

theorem afeHankel_identity_nonreal (s : ℂ) (hs : s.im ≠ 0)
    (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    riemannZeta s - afePolynomial s m =
      afeHankelPrefactor s * ((∮ z in C(0,r), afeHankelKernel s m z) +
        (exp (2*(Real.pi:ℂ)*s*I)-1) *
          ∫ u : ℝ in Ioi r,
            (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by sorry

theorem afeHankel_identity_cutoff (s : ℂ) (hs : s.im ≠ 0)
    (x r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    riemannZeta s - afePolynomial s x =
      afeHankelPrefactor s * ((∮ z in C(0,r), afeHankelKernel s ⌊x⌋₊ z) +
        (exp (2*(Real.pi:ℂ)*s*I)-1) *
          ∫ u : ℝ in Ioi r,
            (u:ℂ)^(s-1)*exp (-((⌊x⌋₊:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by sorry

theorem afeHankel_residue_sum (s : ℂ) (m N : ℕ) :
    afeHankelPrefactor s * (2*(Real.pi:ℂ)*I) *
      (∑ k ∈ Finset.Icc 1 N,
        (residue (afeHankelKernel s m) ((2*Real.pi*k:ℝ)*I) +
         residue (afeHankelKernel s m) (-((2*Real.pi*k:ℝ)*I)))) =
      -pairChi s * afePolynomial (1-s) N := by sorry

end
end HigherCorrelations
