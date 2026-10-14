import HigherCorrelations.PairXiZeros
import HigherCorrelations.PairExactDefinitions
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! Bridge from the entire xi Hadamard formula to the zeta logarithmic derivative.
UNCONDITIONAL. The equality is used off the real axis and away from zeta zeros. -/
namespace HigherCorrelations
noncomputable section
open Complex Filter
open scoped Topology

theorem pairGamma_half_avoid (z : ℂ) (hz : z.im ≠ 0) (a : ℝ) (n : ℕ) :
    z/2+(a:ℂ) ≠ -(n:ℂ) := by
  intro he
  have hh := congrArg Complex.im he
  simp at hh
  exact hz (by linarith)

theorem pairCompleted_eq_xi (z : ℂ) (hz : z.im ≠ 0) :
    pairCompletedFactor z = riemannXi z := by
  have h0 : z ≠ 0 := by intro h; exact hz (by simp [h])
  have h1 : z ≠ 1 := by intro h; exact hz (by simp [h])
  have hΓ : Gamma (z/2) ≠ 0 := Gamma_ne_zero (by
    simpa using pairGamma_half_avoid z hz 0)
  have hp : Complex.exp (-(z/2)*(Real.log Real.pi:ℂ)) = (Real.pi:ℂ)^(-(z/2)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
      ← Complex.ofReal_log Real.pi_pos.le]
    congr 1; ring
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1,
    pairCompletedFactor, hp,
    Gamma_add_one _ (div_ne_zero h0 (by norm_num)), riemannZeta_def_of_ne_zero h0,
    Gammaℝ_def]
  field_simp [hΓ]

theorem pairCompleted_logDeriv (z : ℂ) (hz : z.im ≠ 0) (hζ : riemannZeta z ≠ 0) :
    logDeriv pairCompletedFactor z = 1/(z-1) - (1/2:ℂ)*(Real.log Real.pi:ℂ) +
      (1/2:ℂ)*digamma (z/2+1) + deriv riemannZeta z / riemannZeta z := by
  let p : ℂ → ℂ := fun w => w-1
  let e : ℂ → ℂ := fun w => Complex.exp (-(w/2)*(Real.log Real.pi:ℂ))
  let g : ℂ → ℂ := fun w => Gamma (w/2+1)
  have hp : p z ≠ 0 := by
    intro he
    have he' : z = 1 := sub_eq_zero.mp he
    exact hz (by simp [he'])
  have he : e z ≠ 0 := Complex.exp_ne_zero _
  have hg : g z ≠ 0 := Gamma_ne_zero (by simpa using pairGamma_half_avoid z hz 1)
  have hpd : DifferentiableAt ℂ p z := by dsimp [p]; fun_prop
  have hed : DifferentiableAt ℂ e z := by dsimp [e]; fun_prop
  have hgd : DifferentiableAt ℂ g z :=
    (differentiableAt_Gamma _ (by simpa using pairGamma_half_avoid z hz 1)).comp z (by fun_prop)
  have hzd := differentiableAt_riemannZeta (show z ≠ 1 by intro h; exact hz (by simp [h]))
  have hfun : pairCompletedFactor = (p*e)*g*riemannZeta := rfl
  rw [hfun, _root_.logDeriv_mul (f := (p*e)*g) (g := riemannZeta) z (mul_ne_zero (mul_ne_zero hp he) hg) hζ
    ((hpd.mul hed).mul hgd) hzd,
    _root_.logDeriv_mul (f := p*e) (g := g) z (mul_ne_zero hp he) hg (hpd.mul hed) hgd,
    _root_.logDeriv_mul (f := p) (g := e) z hp he hpd hed]
  have hpl : logDeriv p z = 1/(z-1) := by simp [p, logDeriv_apply]
  have hel : logDeriv e z = -(1/2:ℂ)*(Real.log Real.pi:ℂ) := by
    change logDeriv (Complex.exp ∘ (fun w : ℂ => -(w/2)*(Real.log Real.pi:ℂ))) z = _
    rw [logDeriv_comp (by fun_prop) (by fun_prop)]
    simp
  have hgl : logDeriv g z = (1/2:ℂ)*digamma (z/2+1) := by
    change logDeriv (Gamma ∘ (fun w : ℂ => w/2+1)) z = _
    rw [logDeriv_comp (differentiableAt_Gamma _ (by simpa using pairGamma_half_avoid z hz 1)) (by fun_prop)]
    simp [digamma_def]
    ring
  rw [hpl, hel, hgl, logDeriv_apply]
  ring

theorem pairZeta_logDeriv_xi (z : ℂ) (hz : z.im ≠ 0) (hζ : riemannZeta z ≠ 0) :
    -deriv riemannZeta z / riemannZeta z =
      -logDeriv riemannXi z + 1/(z-1) - (1/2:ℂ)*(Real.log Real.pi:ℂ) +
        (1/2:ℂ)*digamma (z/2+1) := by
  have h1 : z ≠ 1 := by intro h; exact hz (by simp [h])
  have hg := pairGamma_half_avoid z hz 1
  have he : pairCompletedFactor =ᶠ[𝓝 z] riemannXi := by
    filter_upwards [(Complex.continuous_im.continuousAt.eventually_ne hz)] with w hw
    exact pairCompleted_eq_xi w hw
  have hd : logDeriv pairCompletedFactor z = logDeriv riemannXi z := by
    simp only [logDeriv_apply]
    rw [he.deriv_eq, he.eq_of_nhds]
  have h := pairCompleted_logDeriv z hz hζ
  rw [hd] at h
  linear_combination h

theorem pairXi_logDeriv_one_sub (z : ℂ) :
    logDeriv riemannXi (1-z) = -logDeriv riemannXi z := by
  have hf : riemannXi ∘ (fun w : ℂ => 1-w) = riemannXi := funext riemannXi_one_sub
  have h := logDeriv_comp (differentiable_riemannXi (1-z))
    (show DifferentiableAt ℂ (fun w : ℂ => 1-w) z by fun_prop)
  rw [hf] at h
  have h' : logDeriv riemannXi z = -logDeriv riemannXi (1-z) := by simpa using h
  linear_combination h'

theorem pairZeta_logDeriv_functional_eq (z : ℂ) (hz : z.im ≠ 0)
    (hζ : riemannZeta z ≠ 0) (hζr : riemannZeta (1-z) ≠ 0) :
    -deriv riemannZeta z / riemannZeta z =
      deriv riemannZeta (1-z) / riemannZeta (1-z) - (Real.log Real.pi:ℂ) +
        (1/2:ℂ)*(digamma (z/2)+digamma ((1-z)/2)) := by
  have h0 : z ≠ 0 := by intro h; exact hz (by simp [h])
  have h1 : 1-z ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this; exact hz this
  have hr : (1-z).im ≠ 0 := by simpa using hz
  have h := pairZeta_logDeriv_xi z hz hζ
  have h' := pairZeta_logDeriv_xi (1-z) hr hζr
  rw [pairXi_logDeriv_one_sub] at h'
  rw [digamma_apply_add_one _ (by simpa using pairGamma_half_avoid z hz 0)] at h
  rw [digamma_apply_add_one _ (by simpa using pairGamma_half_avoid (1-z) hr 0)] at h'
  have he : 1/(z-1) + 1/(1-z-1) + (1/2:ℂ)*(z/2)⁻¹ + (1/2:ℂ)*((1-z)/2)⁻¹ = 0 := by
    have hz1 : z-1 ≠ 0 := by intro he; exact h1 (by linear_combination -he)
    field_simp [h0,h1,hz1]
    ring
  linear_combination h + h' + he

end
end HigherCorrelations
