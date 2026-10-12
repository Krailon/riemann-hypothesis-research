import HigherCorrelations.ProfileJetBounds
import HigherCorrelations.ProfileIntegral

/-! UNCONDITIONAL differentiation under the integral on the open enlarged cube. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 800000

theorem scalarKernelJet_hasFDerivAt_coordinate (n : ℕ) (x : ℝ) (δ : Fin 3 → ℝ)
    (j : Fin 3) (hj : |δ j| ≤ 3/4) :
    HasFDerivAt (𝕜 := ℝ) (fun η : Fin 3 → ℝ => scalarKernelJet n x (η j))
      ((ContinuousLinearMap.proj j).smulRight (scalarKernelJet (n+1) x (δ j))) δ := by
  convert! (scalarKernelJet_hasDerivAt n x (δ j) hj).hasFDerivAt.comp δ
    (hasFDerivAt_apply (𝕜 := ℝ) j δ) using 1

theorem profileJetIntegrand_hasFDerivAt (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (t : ℝ) (hδ : ∀ j, |δ j| ≤ 3/4) :
    HasFDerivAt (𝕜 := ℝ) (fun η => profileJetIntegrand js a b η t)
      (profileJetDifferential js a b δ t) δ := by
  have h₀ := scalarKernelJet_hasFDerivAt_coordinate (js.count 0) (t-a) δ 0 (hδ 0)
  have h₁ := scalarKernelJet_hasFDerivAt_coordinate (js.count 1) (t-b) δ 1 (hδ 1)
  have h₂ := ((scalarKernelJet_hasDerivAt (js.count 2) t (-δ 2)
    (by simpa using hδ 2)).hasFDerivAt.comp δ (hasFDerivAt_apply (𝕜 := ℝ) 2 δ).neg).const_mul
      ((-1 : ℂ)^js.count 2)
  convert! (h₀.mul h₁).mul h₂ using 1
  ext v
  simp [profileJetDifferential, Fin.sum_univ_three, profileJetIntegrand, List.count_cons,
    pow_succ, Complex.real_smul]
  ring

theorem profileJetDifferential_continuous (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 3/4) :
    Continuous (profileJetDifferential js a b δ) := by
  unfold profileJetDifferential
  apply continuous_finsetSum
  intro j _
  exact (ContinuousLinearMap.smulRightL ℝ (Fin 3 → ℝ) ℂ (ContinuousLinearMap.proj j)).continuous.comp
    (profileJetIntegrand_continuous (j::js) a b δ hδ)

theorem profileJetDifferential_bound (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (t : ℝ) (hδ : ∀ j, |δ j| ≤ 3/4) :
    ‖profileJetDifferential js a b δ t‖ ≤
      3*(4^(js.length+4)*(js.length+1).factorial)/(1+t^2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [profileJetDifferential, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  calc
    _ ≤ ∑ j : Fin 3, ‖v j • profileJetIntegrand (j::js) a b δ t‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖v‖ * (4^(js.length+4)*(js.length+1).factorial/(1+t^2)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      apply mul_le_mul (norm_le_pi_norm v j) _ (norm_nonneg _) (norm_nonneg _)
      simpa [Nat.add_assoc] using profileJetIntegrand_bound (j::js) a b δ t hδ
    _ = _ := by simp; ring

theorem profileJetDifferential_integrable (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 3/4) :
    Integrable (profileJetDifferential js a b δ) := by
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul
    (3*(4^(js.length+4)*(js.length+1).factorial)))
    (profileJetDifferential_continuous js a b δ hδ).aestronglyMeasurable
  filter_upwards [] with t
  simpa [div_eq_mul_inv] using profileJetDifferential_bound js a b δ t hδ

theorem horizontal_cube_mem_nhds (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| < 3/4) :
    {η : Fin 3 → ℝ | ∀ j, |η j| < 3/4} ∈ 𝓝 δ := by
  have hopen : IsOpen {η : Fin 3 → ℝ | ∀ j, |η j| < 3/4} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (by fun_prop) continuous_const)
  exact hopen.mem_nhds hδ

theorem profileJet_hasFDerivAt (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| < 3/4) :
    HasFDerivAt (profileJet js a b) (∫ t : ℝ, profileJetDifferential js a b δ t) δ := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun η t => profileJetIntegrand js a b η t)
    (F' := fun η t => profileJetDifferential js a b η t)
    (bound := fun t => (3*(4^(js.length+4)*(js.length+1).factorial))*(1+t^2)⁻¹)
    (horizontal_cube_mem_nhds δ hδ)
  · filter_upwards [horizontal_cube_mem_nhds δ hδ] with η hη
    exact (profileJetIntegrand_integrable js a b η (fun j => (hη j).le)).aestronglyMeasurable
  · exact profileJetIntegrand_integrable js a b δ (fun j => (hδ j).le)
  · exact (profileJetDifferential_continuous js a b δ (fun j => (hδ j).le)).aestronglyMeasurable
  · filter_upwards [] with t
    intro η hη
    simpa [div_eq_mul_inv] using profileJetDifferential_bound js a b η t (fun j => (hη j).le)
  · exact integrable_inv_one_add_sq.const_mul _
  · filter_upwards [] with t
    intro η hη
    exact profileJetIntegrand_hasFDerivAt js a b η t (fun j => (hη j).le)

theorem profileJet_fderiv_coordinate (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (j : Fin 3) (hδ : ∀ j, |δ j| < 3/4) :
    fderiv ℝ (profileJet js a b) δ (Pi.single j 1) = profileJet (j::js) a b δ := by
  rw [(profileJet_hasFDerivAt js a b δ hδ).fderiv]
  rw [ContinuousLinearMap.integral_apply (profileJetDifferential_integrable js a b δ (fun j => (hδ j).le))]
  simp [profileJetDifferential, profileJet, Pi.single_apply]

theorem horizontalPartial_eq_profileJet (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| < 3/4) :
    horizontalPartial js (horizontalProfile a b) δ = profileJet js a b δ := by
  induction js generalizing δ with
  | nil =>
    have he := integralProfile_eq a b (δ 0) (δ 1) (δ 2)
      (hδ 0).le (hδ 1).le (hδ 2).le
    rw [horizontalPartial, horizontalProfile, ← he]
    unfold profileJet integralProfile
    apply integral_congr_ae
    filter_upwards [] with t
    simp [profileJetIntegrand, profileIntegrand, scalarKernelJet_zero _ _ (hδ 0).le,
      scalarKernelJet_zero _ _ (hδ 1).le, scalarKernelJet_zero _ _ (show |-δ 2| ≤ 3/4 by simpa using (hδ 2).le)]
  | cons j js ih =>
    have he : horizontalPartial js (horizontalProfile a b) =ᶠ[𝓝 δ] profileJet js a b := by
      filter_upwards [horizontal_cube_mem_nhds δ hδ] with η hη
      exact ih η hη
    change fderiv ℝ (horizontalPartial js (horizontalProfile a b)) δ (Pi.single j 1) = _
    rw [he.fderiv_eq]
    exact profileJet_fderiv_coordinate js a b δ j hδ

theorem horizontalPartial_bound (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖horizontalPartial js (horizontalProfile a b) δ‖ ≤ profileDerivativeBound js.length := by
  have hh (j) : |δ j| < 3/4 := lt_of_le_of_lt (hδ j) (by norm_num)
  rw [horizontalPartial_eq_profileJet js a b δ hh]
  exact profileJet_bound js a b δ (fun j => (hh j).le)

end
end HigherCorrelations
