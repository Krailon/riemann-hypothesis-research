import HigherCorrelations.PairErrorDefinitions
import HigherCorrelations.PairContourResidues
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! UNCONDITIONAL functional-equation split in the exact chi convention of
PAIR-EF-001, including the real point w=-1/2. -/
namespace HigherCorrelations
noncomputable section
open Complex Filter
open scoped Topology

theorem pairChi_gamma_avoid (z : ℂ) (hz : z.re < 0) (n : ℕ) :
    1-z ≠ -(n:ℂ) := by
  intro he
  have := congrArg Complex.re he
  simp at this
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem pairChi_functional_eq (z : ℂ) (hz : z.re < 0) :
    riemannZeta z = pairChi z * riemannZeta (1-z) := by
  have h1 : 1-z ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hf := riemannZeta_one_sub (pairChi_gamma_avoid z hz) h1
  rw [show 1-(1-z) = z by ring] at hf
  have hc : cos ((Real.pi:ℂ)*(1-z)/2) = sin ((Real.pi:ℂ)*z/2) := by
    rw [show (Real.pi:ℂ)*(1-z)/2 = (Real.pi:ℂ)/2-(Real.pi:ℂ)*z/2 by ring,
      Complex.cos_pi_div_two_sub]
  have he : 2 * (2*(Real.pi:ℂ))^(-(1-z)) =
      exp (z*(Real.log 2:ℂ)) * exp ((z-1)*(Real.log Real.pi:ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
    have hl : log (2*(Real.pi:ℂ)) = (Real.log 2:ℂ)+(Real.log Real.pi:ℂ) := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
        ← Complex.ofReal_log (by positivity), Real.log_mul (by norm_num) Real.pi_ne_zero]
      push_cast
      rfl
    rw [hl, ← Complex.exp_log (show (2:ℂ) ≠ 0 by norm_num),
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [← Complex.ofNat_log]
    ring
  rw [hf, hc, pairChi, he]
  ring

theorem pairChi_sin_cos_norm (t : ℝ) :
    ‖cos ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2)‖ =
      ‖sin ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2)‖ := by
  let a := (Real.pi:ℂ)*(pairSpectralPoint t-1)/2
  have ha : starRingEnd ℂ a = -((Real.pi:ℂ)/2+a) := by
    dsimp [a, pairSpectralPoint]
    simp only [map_div₀, map_mul, map_sub, map_add, map_one, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  have hs : sin (starRingEnd ℂ a) = -cos a := by
    rw [ha, sin_neg, sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two]
    ring
  have h := congrArg norm hs
  simpa only [Complex.sin_conj, Complex.norm_conj, norm_neg] using h.symm

theorem pairChi_sin_ne_zero (t : ℝ) :
    sin ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2) ≠ 0 := by
  intro hs
  have hn := pairChi_sin_cos_norm t
  rw [hs, norm_zero] at hn
  have hc := norm_eq_zero.mp hn
  have h := Complex.sin_sq_add_cos_sq ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2)
  simp [hs, hc] at h

theorem pairChi_cot_norm (t : ℝ) :
    ‖cot ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2)‖ = 1 := by
  rw [Complex.cot, norm_div, pairChi_sin_cos_norm,
    div_self (norm_ne_zero_iff.mpr (pairChi_sin_ne_zero t))]

theorem pairChi_ne_zero (t : ℝ) : pairChi (pairSpectralPoint t-1) ≠ 0 := by
  unfold pairChi
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (exp_ne_zero _) (exp_ne_zero _))
    (pairChi_sin_ne_zero t)) (Gamma_ne_zero (pairChi_gamma_avoid _ (by
      norm_num [pairSpectralPoint])))

theorem pairChi_differentiable (z : ℂ) (hz : z.re < 0) :
    DifferentiableAt ℂ pairChi z := by
  unfold pairChi
  apply DifferentiableAt.mul (by fun_prop)
  exact (differentiableAt_Gamma _ (pairChi_gamma_avoid z hz)).comp z (by fun_prop)

theorem pairChi_logDeriv (t : ℝ) :
    deriv pairChi (pairSpectralPoint t-1) / pairChi (pairSpectralPoint t-1) =
      (Real.log (2*Real.pi):ℂ) + (Real.pi:ℂ)/2 *
        cot ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2) - digamma (2-pairSpectralPoint t) := by
  let z := pairSpectralPoint t-1
  let a : ℂ → ℂ := fun w => exp (w*(Real.log 2:ℂ))
  let b : ℂ → ℂ := fun w => exp ((w-1)*(Real.log Real.pi:ℂ))
  let c : ℂ → ℂ := fun w => sin ((Real.pi:ℂ)*w/2)
  let d : ℂ → ℂ := fun w => Gamma (1-w)
  have hd : DifferentiableAt ℂ d z :=
    (differentiableAt_Gamma _ (pairChi_gamma_avoid z (by norm_num [z, pairSpectralPoint]))).comp z
      (by fun_prop)
  have hn : d z ≠ 0 := Gamma_ne_zero (pairChi_gamma_avoid z (by norm_num [z, pairSpectralPoint]))
  change logDeriv pairChi z = _
  have hf : pairChi = (a*b)*c*d := rfl
  rw [hf, logDeriv_mul (f := (a*b)*c) (g := d) z
    (mul_ne_zero (mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)) (pairChi_sin_ne_zero t)) hn
    (by dsimp [a,b,c]; fun_prop) hd,
    logDeriv_mul (f := a*b) (g := c) z (mul_ne_zero (exp_ne_zero _) (exp_ne_zero _))
      (pairChi_sin_ne_zero t) (by dsimp [a,b]; fun_prop) (by dsimp [c]; fun_prop),
    logDeriv_mul (f := a) (g := b) z (exp_ne_zero _) (exp_ne_zero _)
      (by dsimp [a]; fun_prop) (by dsimp [b]; fun_prop)]
  have hal : logDeriv a z = (Real.log 2:ℂ) := by
    change logDeriv (exp ∘ (fun w : ℂ => w*(Real.log 2:ℂ))) z = _
    rw [logDeriv_comp (by fun_prop) (by fun_prop)]
    simp
  have hbl : logDeriv b z = (Real.log Real.pi:ℂ) := by
    change logDeriv (exp ∘ (fun w : ℂ => (w-1)*(Real.log Real.pi:ℂ))) z = _
    rw [logDeriv_comp (by fun_prop) (by fun_prop)]
    simp
  have hcl : logDeriv c z = (Real.pi:ℂ)/2 * cot ((Real.pi:ℂ)*z/2) := by
    change logDeriv (sin ∘ (fun w : ℂ => (Real.pi:ℂ)*w/2)) z = _
    rw [logDeriv_comp (by fun_prop) (by fun_prop), Complex.logDeriv_sin]
    simp [mul_comm]
  have hdl : logDeriv d z = -digamma (1-z) := by
    change logDeriv (Gamma ∘ (fun w : ℂ => 1-w)) z = _
    rw [logDeriv_comp (differentiableAt_Gamma _
      (pairChi_gamma_avoid z (by norm_num [z, pairSpectralPoint]))) (by fun_prop)]
    simp [digamma_def]
  rw [hal,hbl,hcl,hdl, Real.log_mul (by norm_num) Real.pi_ne_zero]
  dsimp [z]
  push_cast
  congr 1 <;> ring

theorem pairShift_logDeriv_split (t : ℝ) :
    -deriv riemannZeta (pairSpectralPoint t-1) / riemannZeta (pairSpectralPoint t-1) =
      -deriv pairChi (pairSpectralPoint t-1) / pairChi (pairSpectralPoint t-1) +
        deriv riemannZeta (2-pairSpectralPoint t) / riemannZeta (2-pairSpectralPoint t) := by
  let z := pairSpectralPoint t-1
  have hz : z.re < 0 := by norm_num [z,pairSpectralPoint]
  have he : riemannZeta =ᶠ[𝓝 z] fun w => pairChi w * riemannZeta (1-w) := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz] with w hw
    exact pairChi_functional_eq w hw
  have hr : 1 < (1-z).re := by simp; linarith
  have hne : 1-z ≠ 1 := by intro he; rw [he] at hr; norm_num at hr
  have hd : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (1-w)) z :=
    (differentiableAt_riemannZeta hne).comp z (by fun_prop)
  have h := (logDeriv_congr_nhds he).eq_of_nhds
  change logDeriv riemannZeta z = logDeriv (pairChi * (fun w => riemannZeta (1-w))) z at h
  rw [logDeriv_mul (f := pairChi) (g := fun w => riemannZeta (1-w)) z
    (pairChi_ne_zero t) (riemannZeta_ne_zero_of_one_lt_re hr) (pairChi_differentiable z hz) hd] at h
  have hl : logDeriv (fun w : ℂ => riemannZeta (1-w)) z = -logDeriv riemannZeta (1-z) := by
    change logDeriv (riemannZeta ∘ (fun w : ℂ => 1-w)) z = _
    rw [logDeriv_comp (differentiableAt_riemannZeta hne) (by fun_prop)]
    simp
  rw [hl, show 1-z = 2-pairSpectralPoint t by dsimp [z]; ring] at h
  simp only [logDeriv_apply] at h
  change -deriv riemannZeta z / riemannZeta z = _
  linear_combination -h

end
end HigherCorrelations
