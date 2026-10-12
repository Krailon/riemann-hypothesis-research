import HigherCorrelations.ScalarKernelDerivatives
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! UNCONDITIONAL integrable bounds for ordered horizontal partials of every order. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem profile_counts_sum (js : List (Fin 3)) :
    js.count 0 + js.count 1 + js.count 2 = js.length := by
  induction js with
  | nil => simp
  | cons j js ih => fin_cases j <;> simp_all <;> omega

theorem profile_counts_factorial (js : List (Fin 3)) :
    (js.count 0).factorial * (js.count 1).factorial * (js.count 2).factorial ≤ js.length.factorial := by
  have h₁ := Nat.le_of_dvd (Nat.factorial_pos (js.count 0 + js.count 1))
    (Nat.factorial_mul_factorial_dvd_factorial_add (js.count 0) (js.count 1))
  have h₂ := Nat.le_of_dvd (Nat.factorial_pos (js.count 0 + js.count 1 + js.count 2))
    (Nat.factorial_mul_factorial_dvd_factorial_add (js.count 0 + js.count 1) (js.count 2))
  rw [profile_counts_sum] at h₂
  exact (Nat.mul_le_mul_right _ h₁).trans h₂

theorem profileJetIntegrand_bound (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ) (t : ℝ)
    (hδ : ∀ j, |δ j| ≤ 3/4) :
    ‖profileJetIntegrand js a b δ t‖ ≤ (4^(js.length+3)*js.length.factorial) / (1+t^2) := by
  have hb (n : ℕ) (x e : ℝ) (he : |e| ≤ 3/4) :
      ‖scalarKernelJet n x e‖ ≤ 4^(n+1)*n.factorial := by
    apply (scalarKernelJet_bound n x e he).trans
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg x, show (0:ℝ) ≤ 4^(n+1)*n.factorial by positivity]
  have h₀ := hb (js.count 0) (t-a) (δ 0) (hδ 0)
  have h₁ := hb (js.count 1) (t-b) (δ 1) (hδ 1)
  have h₂ := scalarKernelJet_bound (js.count 2) t (-δ 2) (by simpa using hδ 2)
  have hf : ((js.count 0).factorial : ℝ) * (js.count 1).factorial * (js.count 2).factorial ≤
      js.length.factorial := by exact_mod_cast profile_counts_factorial js
  unfold profileJetIntegrand
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  calc
    _ ≤ (4^(js.count 0+1)*(js.count 0).factorial) *
        (4^(js.count 1+1)*(js.count 1).factorial) *
        ((4^(js.count 2+1)*(js.count 2).factorial)/(1+t^2)) :=
      mul_le_mul (mul_le_mul h₀ h₁ (norm_nonneg _) (by positivity)) h₂ (norm_nonneg _) (by positivity)
    _ = 4^(js.length+3)*(((js.count 0).factorial : ℝ)*(js.count 1).factorial*(js.count 2).factorial)/(1+t^2) := by
      have hp : (4:ℝ)^(js.count 0+1) * 4^(js.count 1+1) * 4^(js.count 2+1) = 4^(js.length+3) := by
        rw [← pow_add, ← pow_add]
        congr 1
        have := profile_counts_sum js
        omega
      linear_combination hp * (((js.count 0).factorial : ℝ)*(js.count 1).factorial*(js.count 2).factorial)/(1+t^2)
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity)

theorem scalarKernelJet_continuous_x (n : ℕ) (e : ℝ) (he : |e| ≤ 3/4) :
    Continuous (fun x => scalarKernelJet n x e) := by
  unfold scalarKernelJet
  apply Continuous.const_mul
  apply Continuous.sub <;> apply Continuous.pow <;> apply Continuous.inv₀ (by fun_prop)
  · intro x; exact (scalar_poles_ne_zero x e he).1
  · intro x; exact (scalar_poles_ne_zero x e he).2

theorem profileJetIntegrand_continuous (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 3/4) : Continuous (profileJetIntegrand js a b δ) := by
  exact (((scalarKernelJet_continuous_x _ _ (hδ 0)).comp (continuous_id.sub continuous_const)).mul
    ((scalarKernelJet_continuous_x _ _ (hδ 1)).comp (continuous_id.sub continuous_const))).mul
    ((scalarKernelJet_continuous_x _ _ (by simpa using hδ 2)).const_mul _)

theorem profileJetIntegrand_integrable (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 3/4) : Integrable (profileJetIntegrand js a b δ) := by
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul (4^(js.length+3)*js.length.factorial))
    (profileJetIntegrand_continuous js a b δ hδ).aestronglyMeasurable
  filter_upwards [] with t
  simpa [div_eq_mul_inv] using profileJetIntegrand_bound js a b δ t hδ

theorem profileJet_bound (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 3/4) : ‖profileJet js a b δ‖ ≤ profileDerivativeBound js.length := by
  have hb := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul
    (4^(js.length+3)*js.length.factorial)) (Filter.Eventually.of_forall
    (fun t => by simpa [div_eq_mul_inv] using profileJetIntegrand_bound js a b δ t hδ))
  simpa [profileJet, profileDerivativeBound, integral_const_mul, integral_univ_inv_one_add_sq] using hb

end
end HigherCorrelations
