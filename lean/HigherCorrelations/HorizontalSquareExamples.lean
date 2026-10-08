import HigherCorrelations.HorizontalSquare

/-! UNCONDITIONAL exact checks. Finite displacement fixtures are SYNTHETIC_MODEL,
not assertions about actual zeta zeros or numerical approximations to cosh.
-/
namespace HigherCorrelations

theorem square_example_mixed_signs :
    (5 / 2 : ℝ) ≤ Real.cosh (-1) * Real.cosh 2 * Real.cosh 0 - 1 := by
  convert cosh_triple_quadratic_lower (-1) 2 0 using 1; norm_num

theorem square_example_empty {I : Type*} (δ : I → ℝ) (b ξ η : ℝ) :
    sameOrdinateCoshSum ∅ δ b ξ η = 0 ∧ horizontalSquareMass ∅ δ = 0 := by
  simp [sameOrdinateCoshSum, horizontalSquareMass]

theorem square_example_singleton {I : Type*} (i : I) (δ : I → ℝ) (b : ℝ) :
    3 * b ^ 2 * (δ i) ^ 2 ≤ sameOrdinateCoshSum {i} δ b 1 1 := by
  have h := same_ordinate_horizontal_square_lower {i} δ b 1 1
  norm_num [horizontalSquareMass, horizontalFrequencyForm] at h
  nlinarith

theorem square_example_zero_scale {I : Type*} (D : Finset I) (δ : I → ℝ) (ξ η : ℝ) :
    sameOrdinateCoshSum D δ 0 ξ η = 0 := by
  simp [sameOrdinateCoshSum, horizontalCoshExcess]

theorem square_example_frequency_origin {I : Type*} (D : Finset I) (δ : I → ℝ) (b : ℝ) :
    sameOrdinateCoshSum D δ b 0 0 = 0 := by
  simp [sameOrdinateCoshSum, horizontalCoshExcess]

theorem square_example_frequency_axes (ξ η : ℝ) :
    horizontalFrequencyForm ξ 0 = ξ ^ 2 ∧ horizontalFrequencyForm 0 η = η ^ 2 ∧
      horizontalFrequencyForm ξ (-ξ) = ξ ^ 2 := by
  dsimp [horizontalFrequencyForm]
  constructor
  · ring
  constructor <;> ring

theorem square_example_repeated_occurrences (b ξ η : ℝ) :
    27 * b ^ 2 * horizontalFrequencyForm ξ η ≤
      sameOrdinateCoshSum Finset.univ (![1, 1, -1] : Fin 3 → ℝ) b ξ η := by
  have h := same_ordinate_horizontal_square_lower Finset.univ
    (![1, 1, -1] : Fin 3 → ℝ) b ξ η
  norm_num [horizontalSquareMass, Fin.sum_univ_succ] at h
  nlinarith

theorem square_example_fiber_multiplicities :
    (ordinateFiber Finset.univ (![0, 0, 1] : Fin 3 → ℕ) 0).card = 2 ∧
    (ordinateFiber Finset.univ (![0, 0, 1] : Fin 3 → ℕ) 1).card = 1 := by decide

end HigherCorrelations
