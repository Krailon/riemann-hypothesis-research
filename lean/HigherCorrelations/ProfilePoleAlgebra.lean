import HigherCorrelations.ProfilePoleLimits
import HigherCorrelations.RationalKernelBounds

/-! UNCONDITIONAL six-pole algebra for distinct centers in the enlarged strip. -/
namespace HigherCorrelations
noncomputable section

theorem profilePole_upper (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4) (i : Fin 3) :
    0 < (profilePole z (i,true)).im := by
  have h := (abs_le.mp (hz i)).1
  simp [profilePole]
  linarith

theorem profilePole_lower (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4) (i : Fin 3) :
    (profilePole z (i,false)).im < 0 := by
  have h := (abs_le.mp (hz i)).2
  simp [profilePole]
  linarith

theorem profilePole_injective (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) : Function.Injective (profilePole z) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ h
  have he : s = t := by
    have hi₁ := profilePole_upper z hz i
    have hi₂ := profilePole_lower z hz i
    have hj₁ := profilePole_upper z hz j
    have hj₂ := profilePole_lower z hz j
    have him := congrArg Complex.im h
    cases s <;> cases t <;> first | rfl | (exfalso; simp_all; linarith)
  subst t
  have hij : i = j := hinj (by simpa [profilePole] using h)
  subst j
  rfl

theorem profilePole_product (z : Fin 3 → ℂ) (v : ℂ) :
    (∏ i : Fin 3 × Bool, (v-profilePole z i)) =
      (1+(v-z 0)^2)*(1+(v-z 1)^2)*(1+(v-z 2)^2) := by
  simp [Fintype.prod_prod_type, Fin.prod_univ_three, profilePole]
  ring_nf
  simp [Complex.I_sq, Complex.I_pow_four]
  ring

theorem profileCenters_bound (a b e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    ∀ i, |(profileCenters a b e f g i).im| ≤ 3/4 := by
  intro i
  fin_cases i <;> simpa [profileCenters] using ‹_›

theorem profileCenters_injective (a b e f g : ℝ)
    (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (profileCenters a b e f g) := by
  intro i j h
  have hr := congrArg Complex.re h
  clear h
  fin_cases i <;> fin_cases j <;> simp_all [profileCenters]

theorem profileIntegrand_eq_poles (a b e f g t : ℝ) :
    profileIntegrand a b e f g t =
      (∏ i : Fin 3 × Bool, ((t : ℂ)-profilePole (profileCenters a b e f g) i))⁻¹ := by
  rw [profilePole_product]
  simp only [profileIntegrand, scalarKernel, profileCenters, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  push_cast
  simp only [mul_inv_rev]
  ring_nf

private theorem prod_erase_as_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (i : ι) :
    (∏ j ∈ Finset.univ.erase i, f j) = ∏ j, if j = i then 1 else f j := by
  classical
  rw [← Finset.prod_erase_mul _ (fun j => if j=i then (1:ℂ) else f j) (Finset.mem_univ i)]
  simp only [ite_true, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

theorem profilePole_coefficient_upper (z : Fin 3 → ℂ) (i : Fin 3) :
    poleCoefficient (profilePole z) (i,true) =
      (2*Complex.I * ∏ j ∈ Finset.univ.erase i, ((z i-z j)*(z i-z j+2*Complex.I)))⁻¹ := by
  unfold poleCoefficient
  rw [prod_erase_as_ite]
  congr 1
  rw [prod_erase_as_ite]
  fin_cases i <;> simp [Fintype.prod_prod_type, Fin.prod_univ_three, profilePole] <;> ring

theorem profilePole_coefficient_lower (z : Fin 3 → ℂ) (i : Fin 3) :
    poleCoefficient (profilePole z) (i,false) =
      (-2*Complex.I * ∏ j ∈ Finset.univ.erase i, ((z i-z j)*(z i-z j-2*Complex.I)))⁻¹ := by
  unfold poleCoefficient
  rw [prod_erase_as_ite]
  congr 1
  rw [prod_erase_as_ite]
  fin_cases i <;> simp [Fintype.prod_prod_type, Fin.prod_univ_three, profilePole] <;> ring

theorem quadratic_factor (z : ℂ) : 4+z^2 = (z+2*Complex.I)*(z-2*Complex.I) := by
  ring_nf
  simp [Complex.I_sq, add_comm]

theorem three_upper_fraction_identity (A B : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : A-B ≠ 0)
    (hAp : A+2*Complex.I ≠ 0) (hAm : A-2*Complex.I ≠ 0)
    (hBp : B+2*Complex.I ≠ 0) (hBm : B-2*Complex.I ≠ 0)
    (hDp : A-B+2*Complex.I ≠ 0) (hDm : A-B-2*Complex.I ≠ 0) :
    1 / ((A-B)*(A-B+2*Complex.I)*A*(A+2*Complex.I)) +
    1 / ((-(A-B))*(-(A-B)+2*Complex.I)*B*(B+2*Complex.I)) +
    1 / ((-A)*(-A+2*Complex.I)*(-B)*(-B+2*Complex.I)) =
      (24+(A-B)^2+A^2+B^2)/((4+(A-B)^2)*(4+A^2)*(4+B^2)) := by
  have hAn : -A+2*Complex.I ≠ 0 := by simpa [neg_sub, sub_eq_add_neg, add_comm] using neg_ne_zero.mpr hAm
  have hBn : -B+2*Complex.I ≠ 0 := by simpa [neg_sub, sub_eq_add_neg, add_comm] using neg_ne_zero.mpr hBm
  have hDn : -(A-B)+2*Complex.I ≠ 0 := by simpa [neg_sub, sub_eq_add_neg, add_comm] using neg_ne_zero.mpr hDm
  have hQA : 4+A^2 ≠ 0 := by rw [quadratic_factor]; exact mul_ne_zero hAp hAm
  have hQB : 4+B^2 ≠ 0 := by rw [quadratic_factor]; exact mul_ne_zero hBp hBm
  have hQD : 4+(A-B)^2 ≠ 0 := by rw [quadratic_factor]; exact mul_ne_zero hDp hDm
  field_simp
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_four]
  ring

theorem center_difference_shifts_ne (z w : ℂ) (hz : |z.im| ≤ 3/4) (hw : |w.im| ≤ 3/4) :
    z-w+2*Complex.I ≠ 0 ∧ z-w-2*Complex.I ≠ 0 := by
  rcases abs_le.mp hz with ⟨hz₁,hz₂⟩
  rcases abs_le.mp hw with ⟨hw₁,hw₂⟩
  constructor <;> intro h <;> have him := congrArg Complex.im h <;> simp at him <;> linarith

theorem center_quadratic_ne (z w : ℂ) (hz : |z.im| ≤ 3/4) (hw : |w.im| ≤ 3/4) :
    4+(z-w)^2 ≠ 0 := by
  rw [quadratic_factor]
  exact mul_ne_zero (center_difference_shifts_ne z w hz hw).1 (center_difference_shifts_ne z w hz hw).2

theorem upper_center_sum (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (Real.pi : ℂ) * (∑ i, (∏ j ∈ Finset.univ.erase i,
      ((z i-z j)*(z i-z j+2*Complex.I)))⁻¹) = rationalKernel (z 0) (z 1) (z 2) := by
  have hn (i j : Fin 3) (hij : i ≠ j) : z i-z j ≠ 0 := sub_ne_zero.mpr (hinj.ne hij)
  have hdiff : (z 0-z 2)-(z 1-z 2) = z 0-z 1 := by ring
  have h := three_upper_fraction_identity (z 0-z 2) (z 1-z 2)
    (hn 0 2 (by decide)) (hn 1 2 (by decide)) (by rw [hdiff]; exact hn 0 1 (by decide))
    (center_difference_shifts_ne _ _ (hz 0) (hz 2)).1 (center_difference_shifts_ne _ _ (hz 0) (hz 2)).2
    (center_difference_shifts_ne _ _ (hz 1) (hz 2)).1 (center_difference_shifts_ne _ _ (hz 1) (hz 2)).2
    (by rw [hdiff]; exact (center_difference_shifts_ne _ _ (hz 0) (hz 1)).1)
    (by rw [hdiff]; exact (center_difference_shifts_ne _ _ (hz 0) (hz 1)).2)
  rw [hdiff] at h
  convert congrArg (fun x : ℂ => (Real.pi : ℂ)*x) h using 1
  · simp [prod_erase_as_ite, Fin.sum_univ_three, Fin.prod_univ_three]
    ring_nf
  · unfold rationalKernel
    ring

theorem lower_center_sum (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (Real.pi : ℂ) * (∑ i, (∏ j ∈ Finset.univ.erase i,
      ((z i-z j)*(z i-z j-2*Complex.I)))⁻¹) = rationalKernel (z 0) (z 1) (z 2) := by
  have hh := upper_center_sum (fun i => -z i) (fun i => by simpa using hz i)
    (fun i j h => hinj (neg_injective h))
  have he (i j : Fin 3) : (-z i - -z j)*(-z i - -z j+2*Complex.I) =
      (z i-z j)*(z i-z j-2*Complex.I) := by ring
  simp_rw [he] at hh
  convert hh using 1
  unfold rationalKernel
  congr 1 <;> ring

theorem profile_pole_sum (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (∑ i : Fin 3 × Bool, poleCoefficient (profilePole z) i *
      (if 0 < (profilePole z i).im then Complex.I*Real.pi else -Complex.I*Real.pi)) =
      rationalKernel (z 0) (z 1) (z 2) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [ite_eq_left (profilePole_upper z hz _), ite_eq_right (not_lt.mpr (profilePole_lower z hz _).le),
    profilePole_coefficient_upper, profilePole_coefficient_lower]
  simp only [mul_inv_rev]
  have h₁ : (2*Complex.I)⁻¹ * (Complex.I*(Real.pi : ℂ)) = (Real.pi : ℂ)/2 := by field_simp
  have h₂ : (-2*Complex.I)⁻¹ * (-Complex.I*(Real.pi : ℂ)) = (Real.pi : ℂ)/2 := by field_simp
  simp only [mul_assoc]
  simp only [mul_inv_rev, mul_assoc] at h₁ h₂
  simp only [h₁, h₂]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have hu := upper_center_sum z hz hinj
  have hl := lower_center_sum z hz hinj
  linear_combination hu / 2 + hl / 2

end
end HigherCorrelations
