import HigherCorrelations.ProfileIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! UNCONDITIONAL smoothness in both real gaps and all three horizontal parameters. -/
namespace HigherCorrelations
noncomputable section
open scoped Topology

theorem rationalProfile_contDiffAt (p : Fin 5 → ℝ)
    (he : |p 2| ≤ 3/4) (hf : |p 3| ≤ 3/4) (hg : |p 4| ≤ 3/4) :
    ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => rationalProfile (q 0) (q 1) (q 2) (q 3) (q 4)) p := by
  have hc (j : Fin 5) : ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => (q j : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_apply ℝ ℝ j).contDiffAt
  unfold rationalProfile rationalKernel
  simp only [div_eq_mul_inv]
  apply ContDiffAt.mul (by fun_prop)
  apply ContDiffAt.inv (by fun_prop)
  have hz := profileCenters_bound (p 0) (p 1) (p 2) (p 3) (p 4) he hf hg
  exact mul_ne_zero (mul_ne_zero (center_quadratic_ne _ _ (hz 0) (hz 1))
    (center_quadratic_ne _ _ (hz 0) (hz 2))) (center_quadratic_ne _ _ (hz 1) (hz 2))

theorem profileRay_contDiffAt (a b : ℝ) (δ : Fin 3 → ℝ) (s : ℝ)
    (hs : ∀ j, |s*δ j| ≤ 3/4) : ContDiffAt ℝ ⊤ (profileRay a b δ) s := by
  have h := rationalProfile_contDiffAt ![a,b,s*δ 0,s*δ 1,s*δ 2] (hs 0) (hs 1) (hs 2)
  have hc : ContDiff ℝ ⊤ (fun t : ℝ => ![a,b,t*δ 0,t*δ 1,t*δ 2]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> simp <;> fun_prop
  convert! h.comp s hc.contDiffAt using 1

theorem integralProfile_contDiffAt (p : Fin 5 → ℝ)
    (he : |p 2| ≤ 1/2) (hf : |p 3| ≤ 1/2) (hg : |p 4| ≤ 1/2) :
    ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => integralProfile (q 0) (q 1) (q 2) (q 3) (q 4)) p := by
  have he' : |p 2| < 3/4 := lt_of_le_of_lt he (by norm_num)
  have hf' : |p 3| < 3/4 := lt_of_le_of_lt hf (by norm_num)
  have hg' : |p 4| < 3/4 := lt_of_le_of_lt hg (by norm_num)
  have heq : (fun q : Fin 5 → ℝ => integralProfile (q 0) (q 1) (q 2) (q 3) (q 4)) =ᶠ[𝓝 p]
      (fun q => rationalProfile (q 0) (q 1) (q 2) (q 3) (q 4)) := by
    have hn (j : Fin 5) (hj : |p j| < 3/4) : ∀ᶠ q : Fin 5 → ℝ in 𝓝 p, |q j| < 3/4 :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds hj
    filter_upwards [hn 2 he', hn 3 hf', hn 4 hg'] with q h₂ h₃ h₄
    exact integralProfile_eq _ _ _ _ _ h₂.le h₃.le h₄.le
  exact (rationalProfile_contDiffAt p he'.le hf'.le hg'.le).congr_of_eventuallyEq heq

end
end HigherCorrelations
