import HigherCorrelations.FiniteDefinitions

/-! UNCONDITIONAL finite algebra underlying the eight-reflection expansion.
The coefficients C and S are arbitrary complex numbers; no integral occurs.
-/
namespace HigherCorrelations

theorem sign_product_expansion (e : Fin 3 → Bool) (C S : Fin 3 → ℂ) :
    (∏ j, (C j + reflectionSign (e j) * S j)) =
      ∑ s : Finset (Fin 3), signCharacter s e * (∏ j ∈ s, S j) * (∏ j ∈ sᶜ, C j) := by
  simpa [add_comm, Finset.prod_mul_distrib, signCharacter] using
    Fintype.prod_add (fun j => reflectionSign (e j) * S j) C

theorem weighted_sign_product (K : (Fin 3 → Bool) → ℂ) (C S : Fin 3 → ℂ) :
    (1 / 8 : ℂ) * ∑ e, K e * (∏ j, (C j + reflectionSign (e j) * S j)) =
      ∑ s : Finset (Fin 3), signCoefficient K s * (∏ j ∈ s, S j) * (∏ j ∈ sᶜ, C j) := by
  simp only [sign_product_expansion, signCoefficient, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem weighted_sign_sub_one (K : (Fin 3 → Bool) → ℂ) (C S : Fin 3 → ℂ) :
    (1 / 8 : ℂ) * ∑ e, K e * ((∏ j, (C j + reflectionSign (e j) * S j)) - 1) =
      (∑ s : Finset (Fin 3), signCoefficient K s * (∏ j ∈ s, S j) *
        (∏ j ∈ sᶜ, C j)) - signCoefficient K ∅ := by
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, mul_sub, weighted_sign_product]
  simp [signCoefficient, signCharacter]

theorem weighted_sign_empty_split (K : (Fin 3 → Bool) → ℂ) (C S : Fin 3 → ℂ) :
    (1 / 8 : ℂ) * ∑ e, K e * ((∏ j, (C j + reflectionSign (e j) * S j)) - 1) =
      signCoefficient K ∅ * ((∏ j, C j) - 1) +
      ∑ s ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
        signCoefficient K s * (∏ j ∈ s, S j) * (∏ j ∈ sᶜ, C j) := by
  rw [weighted_sign_sub_one]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset (Fin 3)))]
  simp only [Finset.prod_empty, mul_one, Finset.compl_empty]
  ring

end HigherCorrelations
