import HigherCorrelations.ProfileDirectional
import Mathlib.Analysis.Calculus.Taylor

/-! UNCONDITIONAL second and fourth order horizontal replacement remainders. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem profileRay_contDiffOn (a b : ℝ) (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 1/2) :
    ContDiffOn ℝ ⊤ (profileRay a b δ) (Set.Icc (0 : ℝ) 1) := by
  intro s hs
  apply ContDiffAt.contDiffWithinAt
  apply profileRay_contDiffAt
  intro j
  have hab : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hh : |s*δ j| ≤ 1/2 := by
    rw [abs_mul]
    simpa using mul_le_mul hab (hδ j) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  linarith

theorem profileRay_iteratedDerivWithin (n : ℕ) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDerivWithin n (profileRay a b δ) (Set.Icc 0 1) s =
      iteratedDeriv n (profileRay a b δ) s := by
  apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num)) _ hs
  apply (profileRay_contDiffAt a b δ s _).of_le le_top
  intro j
  have hab : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hh : |s*δ j| ≤ 1/2 := by
    rw [abs_mul]
    simpa using mul_le_mul hab (hδ j) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  linarith

theorem profile_taylor_remainder_bound (n : ℕ) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖profileRay a b δ 1 - taylorWithinEval (profileRay a b δ) n (Set.Icc 0 1) 0 1‖ ≤
      profileDerivativeBound (n+1) * horizontalSize δ ^ (n+1) / (n+1).factorial := by
  have hc : ContDiffOn ℝ (n+1 : ℕ) (profileRay a b δ) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (profileRay_contDiffOn a b δ hδ).of_le le_top
  have hr := taylor_integral_remainder hc
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hr
  rw [hr]
  let C := profileDerivativeBound (n+1) * horizontalSize δ ^ (n+1)
  have hbound : ∀ᵐ t : ℝ, t ∈ Set.Ioc 0 1 →
      ‖((1-t)^n/(n.factorial : ℝ)) • iteratedDerivWithin (n+1) (profileRay a b δ) (Set.Icc 0 1) t‖ ≤
        ((1-t)^n/(n.factorial : ℝ))*C := by
    filter_upwards [] with t
    intro ht
    have htpos : 0 ≤ 1-t := sub_nonneg.mpr ht.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1-t)^n/(n.factorial : ℝ)),
      profileRay_iteratedDerivWithin _ a b δ hδ t ⟨ht.1.le,ht.2⟩]
    exact mul_le_mul_of_nonneg_left (profileRay_derivative_bound (n+1) a b δ t hδ
      (abs_le.mpr ⟨by linarith [ht.1],ht.2⟩)) (by positivity)
  have hi : IntervalIntegrable (fun t : ℝ => ((1-t)^n/(n.factorial : ℝ))*C) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => ((1-t)^n/(n.factorial : ℝ))*C)).intervalIntegrable _ _
  apply (intervalIntegral.norm_integral_le_of_norm_le (by norm_num) hbound hi).trans_eq
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^n) 1]
  simp only [integral_pow, sub_self, sub_zero, one_pow, zero_pow (Nat.succ_ne_zero n),
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, C]
  field_simp

theorem profileDirectionalJet_neg_at_zero (n : ℕ) (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) : profileDirectionalJet n js a b (-δ) 0 =
      (-1 : ℂ)^n * profileDirectionalJet n js a b δ 0 := by
  induction n generalizing js with
  | zero => simp [profileDirectionalJet]
  | succ n ih =>
    simp only [profileDirectionalJet, Pi.neg_apply, Complex.ofReal_neg, ih, pow_succ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem profileTaylor_one (a b : ℝ) (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 1/2) :
    taylorWithinEval (profileRay a b δ) 1 (Set.Icc 0 1) 0 1 =
      horizontalProfile a b 0 + profileDirectionalJet 1 [] a b δ 0 := by
  rw [show (1 : ℕ) = 0+1 from rfl, taylorWithinEval_succ]
  rw [profileRay_iteratedDerivWithin _ a b δ hδ 0 (by simp),
    profileRay_iteratedDeriv _ a b δ 0 (by intro j; simp)]
  simp [profileRay]

theorem profileTaylor_three (a b : ℝ) (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 1/2) :
    taylorWithinEval (profileRay a b δ) 3 (Set.Icc 0 1) 0 1 =
      horizontalProfile a b 0 + profileDirectionalJet 1 [] a b δ 0 +
      profileDirectionalJet 2 [] a b δ 0 / 2 + profileDirectionalJet 3 [] a b δ 0 / 6 := by
  rw [taylorWithinEval_succ (profileRay a b δ) 2,
    taylorWithinEval_succ (profileRay a b δ) 1, profileTaylor_one a b δ hδ]
  rw [profileRay_iteratedDerivWithin _ a b δ hδ 0 (by simp),
    profileRay_iteratedDerivWithin _ a b δ hδ 0 (by simp),
    profileRay_iteratedDeriv _ a b δ 0 (by intro j; simp),
    profileRay_iteratedDeriv _ a b δ 0 (by intro j; simp)]
  norm_num [Complex.real_smul]
  ring

private theorem norm_average_le (u v : ℂ) (B : ℝ) (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    ‖(u+v)/2‖ ≤ B := by
  rw [norm_div]
  norm_num
  have hh := norm_add_le u v
  linarith

theorem profile_symmetric_second_bound (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖(horizontalProfile a b δ + horizontalProfile a b (-δ))/2 - horizontalProfile a b 0‖ ≤
      profileDerivativeBound 2 * horizontalSize δ ^ 2 / 2 := by
  have hn (j) : |(-δ) j| ≤ 1/2 := by simpa using hδ j
  have hp := profile_taylor_remainder_bound 1 a b δ hδ
  have hm := profile_taylor_remainder_bound 1 a b (-δ) hn
  rw [profileTaylor_one a b δ hδ] at hp
  rw [profileTaylor_one a b (-δ) hn, profileDirectionalJet_neg_at_zero] at hm
  simp only [profileRay, one_smul, horizontalSize, Pi.neg_apply, abs_neg] at hp hm
  norm_num at hp hm
  convert norm_average_le _ _ _ hp hm using 1 <;> congr 1
  ring

theorem profile_symmetric_fourth_bound (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖(horizontalProfile a b δ + horizontalProfile a b (-δ))/2 - horizontalProfile a b 0 -
        iteratedDeriv 2 (profileRay a b δ) 0 / 2‖ ≤
      profileDerivativeBound 4 * horizontalSize δ ^ 4 / 24 := by
  have hn (j) : |(-δ) j| ≤ 1/2 := by simpa using hδ j
  have hp := profile_taylor_remainder_bound 3 a b δ hδ
  have hm := profile_taylor_remainder_bound 3 a b (-δ) hn
  rw [profileTaylor_three a b δ hδ] at hp
  rw [profileTaylor_three a b (-δ) hn] at hm
  simp only [profileDirectionalJet_neg_at_zero] at hm
  simp only [profileRay, one_smul, horizontalSize, Pi.neg_apply, abs_neg] at hp hm
  norm_num at hp hm
  rw [profileRay_iteratedDeriv 2 a b δ 0 (by intro j; simp)]
  convert norm_average_le _ _ _ hp hm using 1 <;> congr 1
  ring

end
end HigherCorrelations
