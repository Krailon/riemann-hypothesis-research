import HigherCorrelations.PairZeroDefinitions
import HigherCorrelations.ProfilePoleAlgebra

/-! UNCONDITIONAL four-pole algebra for the pair kernel. -/
namespace HigherCorrelations
noncomputable section
theorem pairKernelPole_upper (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4) (i : Fin 2) :
    0 < (pairKernelPole z (i,true)).im := by
  have h := (abs_le.mp (hz i)).1
  simp [pairKernelPole]
  linarith

theorem pairKernelPole_lower (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4) (i : Fin 2) :
    (pairKernelPole z (i,false)).im < 0 := by
  have h := (abs_le.mp (hz i)).2
  simp [pairKernelPole]
  linarith

theorem pairKernelPole_injective (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) : Function.Injective (pairKernelPole z) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ h
  have he : s = t := by
    have hi₁ := pairKernelPole_upper z hz i
    have hi₂ := pairKernelPole_lower z hz i
    have hj₁ := pairKernelPole_upper z hz j
    have hj₂ := pairKernelPole_lower z hz j
    have him := congrArg Complex.im h
    cases s <;> cases t <;> first | rfl | (exfalso; simp_all; linarith)
  subst t
  have hij : i = j := hinj (by simpa [pairKernelPole] using h)
  subst j
  rfl

theorem pairKernelPole_product (z : Fin 2 → ℂ) (v : ℂ) :
    (∏ i : Fin 2 × Bool, (v-pairKernelPole z i)) =
      (1+(v-z 0)^2)*(1+(v-z 1)^2) := by
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, pairKernelPole]
  ring_nf
  simp [Complex.I_sq, Complex.I_pow_four]
  ring

private theorem prod_erase_as_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (i : ι) :
    (∏ j ∈ Finset.univ.erase i, f j) = ∏ j, if j = i then 1 else f j := by
  classical
  rw [← Finset.prod_erase_mul _ (fun j => if j=i then (1:ℂ) else f j) (Finset.mem_univ i)]
  simp only [ite_true, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

theorem pairKernelPole_coefficient_upper (z : Fin 2 → ℂ) (i : Fin 2) :
    poleCoefficient (pairKernelPole z) (i,true) =
      (2*Complex.I * ∏ j ∈ Finset.univ.erase i, ((z i-z j)*(z i-z j+2*Complex.I)))⁻¹ := by
  unfold poleCoefficient
  rw [prod_erase_as_ite]
  congr 1
  rw [prod_erase_as_ite]
  fin_cases i <;> simp [Fintype.prod_prod_type, Fin.prod_univ_two, pairKernelPole] <;> ring

theorem pairKernelPole_coefficient_lower (z : Fin 2 → ℂ) (i : Fin 2) :
    poleCoefficient (pairKernelPole z) (i,false) =
      (-2*Complex.I * ∏ j ∈ Finset.univ.erase i, ((z i-z j)*(z i-z j-2*Complex.I)))⁻¹ := by
  unfold poleCoefficient
  rw [prod_erase_as_ite]
  congr 1
  rw [prod_erase_as_ite]
  fin_cases i <;> simp [Fintype.prod_prod_type, Fin.prod_univ_two, pairKernelPole] <;> ring


theorem pairKernel_upper_sum (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (Real.pi : ℂ) * (∑ i, (∏ j ∈ Finset.univ.erase i,
      ((z i-z j)*(z i-z j+2*Complex.I)))⁻¹) = 2*Real.pi/(4+(z 0-z 1)^2) := by
  have hd : z 0-z 1 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have hn : z 1-z 0 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have hp := (center_difference_shifts_ne _ _ (hz 0) (hz 1)).1
  have hm := (center_difference_shifts_ne _ _ (hz 1) (hz 0)).1
  have hq := center_quadratic_ne _ _ (hz 0) (hz 1)
  simp only [Fin.sum_univ_two]
  simp [prod_erase_as_ite, Fin.prod_univ_two]
  field_simp
  ring_nf
  simp [Complex.I_sq, Complex.I_pow_four]
  ring

theorem pairKernel_lower_sum (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (Real.pi : ℂ) * (∑ i, (∏ j ∈ Finset.univ.erase i,
      ((z i-z j)*(z i-z j-2*Complex.I)))⁻¹) = 2*Real.pi/(4+(z 0-z 1)^2) := by
  have h := pairKernel_upper_sum (fun i => -z i) (fun i => by simpa using hz i)
    (fun i j h => hinj (neg_injective h))
  have he (i j : Fin 2) : (-z i - -z j)*(-z i - -z j+2*Complex.I) =
      (z i-z j)*(z i-z j-2*Complex.I) := by ring
  simp_rw [he] at h
  convert h using 1
  congr 2
  ring

theorem pairKernel_pole_sum (z : Fin 2 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (∑ i : Fin 2 × Bool, poleCoefficient (pairKernelPole z) i *
      (if 0 < (pairKernelPole z i).im then Complex.I*Real.pi else -Complex.I*Real.pi)) =
      2*Real.pi/(4+(z 0-z 1)^2) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [ite_eq_left (pairKernelPole_upper z hz _),
    ite_eq_right (not_lt.mpr (pairKernelPole_lower z hz _).le),
    pairKernelPole_coefficient_upper, pairKernelPole_coefficient_lower]
  simp only [mul_inv_rev]
  have h₁ : (2*Complex.I)⁻¹ * (Complex.I*(Real.pi : ℂ)) = (Real.pi : ℂ)/2 := by field_simp
  have h₂ : (-2*Complex.I)⁻¹ * (-Complex.I*(Real.pi : ℂ)) = (Real.pi : ℂ)/2 := by field_simp
  simp only [mul_assoc]
  simp only [mul_inv_rev, mul_assoc] at h₁ h₂
  simp only [h₁,h₂]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have hu := pairKernel_upper_sum z hz hinj
  have hl := pairKernel_lower_sum z hz hinj
  linear_combination hu / 2 + hl / 2

end
end HigherCorrelations
