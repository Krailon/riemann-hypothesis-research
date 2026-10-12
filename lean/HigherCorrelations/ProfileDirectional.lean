import HigherCorrelations.ProfileJetDerivatives
import HigherCorrelations.ProfileSmoothness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! UNCONDITIONAL directional derivatives with explicit uniform constants. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory
open scoped Topology

theorem profileJet_fderiv_apply (js : List (Fin 3)) (a b : ℝ)
    (δ v : Fin 3 → ℝ) (hδ : ∀ j, |δ j| < 3/4) :
    fderiv ℝ (profileJet js a b) δ v = ∑ j, (v j : ℂ)*profileJet (j::js) a b δ := by
  have hv : v = ∑ j : Fin 3, v j • Pi.single j (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, profileJet_fderiv_coordinate js a b δ _ hδ, Complex.real_smul]

theorem profileDirectionalJet_hasDerivAt (n : ℕ) (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (s : ℝ) (hs : ∀ j, |s*δ j| < 3/4) :
    HasDerivAt (profileDirectionalJet n js a b δ)
      (profileDirectionalJet (n+1) js a b δ s) s := by
  induction n generalizing js with
  | zero =>
    have hc : HasDerivAt (fun t : ℝ => t • δ) δ s := by
      simpa using (hasDerivAt_id s).smul_const δ
    have hf := (profileJet_hasFDerivAt js a b (s • δ) hs).comp_hasDerivAt s hc
    have he := profileJet_fderiv_apply js a b (s • δ) δ hs
    rw [(profileJet_hasFDerivAt js a b (s • δ) hs).fderiv] at he
    simpa [profileDirectionalJet, Function.comp_def, he] using hf
  | succ n ih =>
    simpa only [profileDirectionalJet] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (ih (j::js)).const_mul (δ j : ℂ))

theorem profileDirectionalJet_bound (n : ℕ) (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (s : ℝ) (hs : ∀ j, |s*δ j| ≤ 3/4) :
    ‖profileDirectionalJet n js a b δ s‖ ≤
      profileDerivativeBound (n+js.length) * horizontalSize δ ^ n := by
  induction n generalizing js with
  | zero => simpa [profileDirectionalJet] using profileJet_bound js a b (s • δ) hs
  | succ n ih =>
    calc
      _ ≤ ∑ j : Fin 3, ‖(δ j : ℂ)*profileDirectionalJet n (j::js) a b δ s‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, |δ j| * (profileDerivativeBound (n+1+js.length) * horizontalSize δ ^ n) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (j::js)
      _ = _ := by rw [← Finset.sum_mul]; simp [horizontalSize, pow_succ]; ring

theorem profile_ray_cube_mem_nhds (δ : Fin 3 → ℝ) (s : ℝ) (hs : ∀ j, |s*δ j| < 3/4) :
    {t : ℝ | ∀ j, |t*δ j| < 3/4} ∈ 𝓝 s := by
  have hopen : IsOpen {t : ℝ | ∀ j, |t*δ j| < 3/4} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (by fun_prop) continuous_const)
  exact hopen.mem_nhds hs

theorem profileRay_iteratedDeriv (n : ℕ) (a b : ℝ) (δ : Fin 3 → ℝ) (s : ℝ)
    (hs : ∀ j, |s*δ j| < 3/4) :
    iteratedDeriv n (profileRay a b δ) s = profileDirectionalJet n [] a b δ s := by
  induction n generalizing s with
  | zero =>
    exact horizontalPartial_eq_profileJet [] a b (s • δ) hs
  | succ n ih =>
    have he : iteratedDeriv n (profileRay a b δ) =ᶠ[𝓝 s] profileDirectionalJet n [] a b δ := by
      filter_upwards [profile_ray_cube_mem_nhds δ s hs] with t ht
      exact ih t ht
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (profileDirectionalJet_hasDerivAt n [] a b δ s hs).deriv

theorem profileRay_derivative_bound (n : ℕ) (a b : ℝ) (δ : Fin 3 → ℝ) (s : ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) (hs : |s| ≤ 1) :
    ‖iteratedDeriv n (profileRay a b δ) s‖ ≤ profileDerivativeBound n * horizontalSize δ ^ n := by
  have hh (j) : |s*δ j| ≤ 1/2 := by
    rw [abs_mul]
    simpa using mul_le_mul hs (hδ j) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have ho (j) : |s*δ j| < 3/4 := lt_of_le_of_lt (hh j) (by norm_num)
  rw [profileRay_iteratedDeriv n a b δ s ho]
  simpa using profileDirectionalJet_bound n [] a b δ s (fun j => (ho j).le)

end
end HigherCorrelations
