import HigherCorrelations.ApproximateFunctionalDefinitions
import HigherCorrelations.PairChiIdentity
import HigherCorrelations.ZeroReflection
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! UNCONDITIONAL identities for the actual sharp-cutoff remainder. These
identities do not assume or prove the analytic approximate-functional-equation
remainder estimate. -/
namespace HigherCorrelations
noncomputable section
open Complex
open scoped ComplexConjugate

theorem afePoint_re (σ t : ℝ) : (afePoint σ t).re = σ := by
  simp [afePoint]

theorem afePoint_im (σ t : ℝ) : (afePoint σ t).im = t := by
  simp [afePoint]

theorem afePoint_reflect (σ t : ℝ) : 1-afePoint σ t = afePoint (1-σ) (-t) := by
  simp [afePoint]; ring

theorem afePoint_conj (σ t : ℝ) : conj (afePoint σ t) = afePoint σ (-t) := by
  simp [afePoint]

theorem afePolynomial_nat (s : ℂ) (N : ℕ) :
    afePolynomial s N = ∑ n ∈ Finset.Icc 1 N, (n : ℂ)^(-s) := by
  simp [afePolynomial]

theorem afePolynomial_one (s : ℂ) : afePolynomial s 1 = 1 := by
  simp [afePolynomial]

theorem afePolynomial_lt_one (s : ℂ) {x : ℝ} (hx : x < 1) :
    afePolynomial s x = 0 := by
  have hf : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [afePolynomial, hf]

theorem afePolynomial_conj (s : ℂ) (x : ℝ) :
    afePolynomial (conj s) x = conj (afePolynomial s x) := by
  simp only [afePolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [← map_neg]
  have he := cpow_conj (n : ℂ) (-s) (by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hp.le]
    exact Real.pi_ne_zero.symm)
  simpa using he

theorem afe_identity (s : ℂ) (x y : ℝ) :
    riemannZeta s = afePolynomial s x + pairChi s * afePolynomial (1-s) y +
      afeRemainder s x y := by
  unfold afeRemainder; ring

theorem afe_phase_identity (σ t x y : ℝ) :
    riemannZeta (afePoint σ t) = afePolynomial (afePoint σ t) x +
      afePhase σ t * afePolynomial (1-afePoint σ t) y +
      afePhaseRemainder σ t x y := by
  unfold afePhaseRemainder; ring

theorem afe_phase_remainder_split (σ t x y : ℝ) :
    afePhaseRemainder σ t x y = afeRemainder (afePoint σ t) x y +
      (pairChi (afePoint σ t)-afePhase σ t) * afePolynomial (1-afePoint σ t) y := by
  unfold afePhaseRemainder afeRemainder; ring

theorem afe_phase_remainder_bound (σ t x y : ℝ) :
    ‖afePhaseRemainder σ t x y‖ ≤ ‖afeRemainder (afePoint σ t) x y‖ +
      ‖pairChi (afePoint σ t)-afePhase σ t‖ * ‖afePolynomial (1-afePoint σ t) y‖ := by
  rw [afe_phase_remainder_split, ← norm_mul]
  exact norm_add_le _ _

theorem afeChi_functional_eq (s : ℂ) (hs : s.im ≠ 0) :
    riemannZeta s = pairChi s * riemannZeta (1-s) := by
  have havoid (n : ℕ) : 1-s ≠ -(n:ℂ) := by
    intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have hone : 1-s ≠ 1 := by
    intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have hf := riemannZeta_one_sub havoid hone
  rw [show 1-(1-s) = s by ring] at hf
  have hc : cos ((Real.pi:ℂ)*(1-s)/2) = sin ((Real.pi:ℂ)*s/2) := by
    rw [show (Real.pi:ℂ)*(1-s)/2 = (Real.pi:ℂ)/2-(Real.pi:ℂ)*s/2 by ring,
      Complex.cos_pi_div_two_sub]
  have he : 2 * (2*(Real.pi:ℂ))^(-(1-s)) =
      exp (s*(Real.log 2:ℂ)) * exp ((s-1)*(Real.log Real.pi:ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
    have hl : log (2*(Real.pi:ℂ)) = (Real.log 2:ℂ)+(Real.log Real.pi:ℂ) := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
        ← Complex.ofReal_log (by positivity), Real.log_mul (by norm_num) Real.pi_ne_zero]
      push_cast; rfl
    rw [hl, ← Complex.exp_log (show (2:ℂ) ≠ 0 by norm_num),
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1; rw [← Complex.ofNat_log]; ring
  rw [hf, hc, pairChi, he]; ring

theorem afeChi_conj (s : ℂ) : pairChi (conj s) = conj (pairChi s) := by
  have htwo : conj (2:ℂ) = 2 := Complex.conj_ofReal 2
  simp only [pairChi, map_mul, map_sub, map_one, ← exp_conj, ← sin_conj, ← Gamma_conj,
    conj_ofReal, map_div₀, htwo]

theorem afeRemainder_conj (s : ℂ) (x y : ℝ) :
    afeRemainder (conj s) x y = conj (afeRemainder s x y) := by
  have he : 1-conj s = conj (1-s) := by simp
  unfold afeRemainder
  rw [he, riemannZeta_conj, afePolynomial_conj, afeChi_conj, afePolynomial_conj]
  simp

theorem afeChi_reflection (s : ℂ) (hs : s.im ≠ 0) : pairChi s * pairChi (1-s) = 1 := by
  have havoid (n : ℕ) : s ≠ -(n:ℂ) := by
    intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have havoid' (n : ℕ) : 1-s ≠ -(n:ℂ) := by
    intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have hsin : sin ((Real.pi:ℂ)*s) ≠ 0 := by
    intro h
    have hg := Gamma_mul_Gamma_one_sub s
    rw [h, div_zero] at hg
    exact mul_ne_zero (Gamma_ne_zero havoid) (Gamma_ne_zero havoid') hg
  have hc : sin ((Real.pi:ℂ)*(1-s)/2) = cos ((Real.pi:ℂ)*s/2) := by
    rw [show (Real.pi:ℂ)*(1-s)/2 = (Real.pi:ℂ)/2-(Real.pi:ℂ)*s/2 by ring,
      Complex.sin_pi_div_two_sub]
  have ht : 2 * sin ((Real.pi:ℂ)*s/2) * cos ((Real.pi:ℂ)*s/2) =
      sin ((Real.pi:ℂ)*s) := by
    rw [← sin_two_mul]; congr 1; ring
  have he : exp (s*(Real.log 2:ℂ)) * exp ((s-1)*(Real.log Real.pi:ℂ)) *
      (exp ((1-s)*(Real.log 2:ℂ)) * exp (((1-s)-1)*(Real.log Real.pi:ℂ))) =
      2 / (Real.pi:ℂ) := by
    rw [← exp_add, ← exp_add, ← exp_add]
    rw [show s*(Real.log 2:ℂ) + (s-1)*(Real.log Real.pi:ℂ) +
      ((1-s)*(Real.log 2:ℂ) + ((1-s)-1)*(Real.log Real.pi:ℂ)) =
        (Real.log 2:ℂ) - (Real.log Real.pi:ℂ) by ring, exp_sub]
    norm_cast
    rw [Real.exp_log (by norm_num), Real.exp_log Real.pi_pos]
  unfold pairChi
  rw [hc, show 1-(1-s)=s by ring]
  calc
    _ = (exp (s*(Real.log 2:ℂ)) * exp ((s-1)*(Real.log Real.pi:ℂ)) *
        (exp ((1-s)*(Real.log 2:ℂ)) * exp (((1-s)-1)*(Real.log Real.pi:ℂ)))) *
        (sin ((Real.pi:ℂ)*s/2) * cos ((Real.pi:ℂ)*s/2)) *
        (Gamma s * Gamma (1-s)) := by ring
    _ = (2/(Real.pi:ℂ)) * (sin ((Real.pi:ℂ)*s)/2) *
        ((Real.pi:ℂ)/sin ((Real.pi:ℂ)*s)) := by
      rw [he, Gamma_mul_Gamma_one_sub]
      congr 2
      apply (eq_div_iff (by norm_num : (2:ℂ) ≠ 0)).mpr
      linear_combination ht
    _ = 1 := by field_simp

theorem afeRemainder_reflection (s : ℂ) (hs : s.im ≠ 0) (x y : ℝ) :
    afeRemainder s y x = pairChi s * afeRemainder (1-s) x y := by
  have hf := afeChi_functional_eq s hs
  have hc := afeChi_reflection s hs
  unfold afeRemainder
  rw [show 1-(1-s)=s by ring]
  linear_combination hf + afePolynomial s y * hc

theorem afeRemainder_reflection_norm (s : ℂ) (hs : s.im ≠ 0) (x y : ℝ) :
    ‖afeRemainder s y x‖ = ‖pairChi s‖ * ‖afeRemainder (1-s) x y‖ := by
  rw [afeRemainder_reflection s hs, norm_mul]

theorem afeChi_critical_norm {t : ℝ} (ht : t ≠ 0) : ‖pairChi (afePoint (1/2) t)‖ = 1 := by
  have hs : (afePoint (1/2) t).im ≠ 0 := by simpa [afePoint] using ht
  have he : 1-afePoint (1/2) t = conj (afePoint (1/2) t) := by
    rw [afePoint_reflect, afePoint_conj]
    norm_num
  have h := afeChi_reflection (afePoint (1/2) t) hs
  rw [he, afeChi_conj] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_conj, norm_one] at hn
  have := norm_nonneg (pairChi (afePoint (1/2) t))
  nlinarith

end
end HigherCorrelations
