import HigherCorrelations.HorizontalSquareDefinitions

/-! Specifications only: intentional sorry terms; no solution imports this file. -/
namespace HigherCorrelations

theorem cosh_quadratic_lower (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by sorry

theorem cosh_triple_quadratic_lower (a₀ a₁ a₂ : ℝ) :
    (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2) / 2 ≤
      Real.cosh a₀ * Real.cosh a₁ * Real.cosh a₂ - 1 := by sorry

theorem horizontal_cosh_square_lower (b ξ η d₀ d₁ d₂ : ℝ) :
    b ^ 2 / 2 * (d₀ ^ 2 * (ξ + η) ^ 2 + d₁ ^ 2 * ξ ^ 2 + d₂ ^ 2 * η ^ 2) ≤
      horizontalCoshExcess b ξ η d₀ d₁ d₂ := by sorry

theorem horizontal_frequency_lower (ξ η : ℝ) :
    (ξ ^ 2 + η ^ 2) / 2 ≤ horizontalFrequencyForm ξ η := by sorry

theorem horizontal_frequency_nonneg (ξ η : ℝ) : 0 ≤ horizontalFrequencyForm ξ η := by sorry

theorem horizontal_frequency_zero_iff (ξ η : ℝ) :
    horizontalFrequencyForm ξ η = 0 ↔ ξ = 0 ∧ η = 0 := by sorry

theorem horizontal_square_mass_nonneg {I : Type*} (D : Finset I) (δ : I → ℝ) :
    0 ≤ horizontalSquareMass D δ := by sorry

theorem horizontal_cube_square_sum {I : Type*} (D : Finset I) (δ : I → ℝ) (ξ η : ℝ) :
    (∑ i ∈ D, ∑ j ∈ D, ∑ k ∈ D,
      ((δ i) ^ 2 * (ξ + η) ^ 2 + (δ j) ^ 2 * ξ ^ 2 + (δ k) ^ 2 * η ^ 2)) =
      2 * (D.card : ℝ) ^ 2 * horizontalSquareMass D δ * horizontalFrequencyForm ξ η := by sorry

theorem same_ordinate_horizontal_square_lower {I : Type*}
    (D : Finset I) (δ : I → ℝ) (b ξ η : ℝ) :
    b ^ 2 * (D.card : ℝ) ^ 2 * horizontalSquareMass D δ * horizontalFrequencyForm ξ η ≤
      sameOrdinateCoshSum D δ b ξ η := by sorry

theorem same_ordinate_cosh_nonneg {I : Type*}
    (D : Finset I) (δ : I → ℝ) (b ξ η : ℝ) : 0 ≤ sameOrdinateCoshSum D δ b ξ η := by sorry

theorem weighted_ordinate_fibers_lower {I A : Type*} [DecidableEq A]
    (D : Finset I) (γ : I → A) (δ : I → ℝ) (W : A → ℝ)
    (hW : ∀ g ∈ D.image γ, 0 ≤ W g) (b ξ η : ℝ) :
    b ^ 2 * horizontalFrequencyForm ξ η *
      (∑ g ∈ D.image γ, W g * ((ordinateFiber D γ g).card : ℝ) ^ 2 *
        horizontalSquareMass (ordinateFiber D γ g) δ) ≤
      ∑ g ∈ D.image γ, W g * sameOrdinateCoshSum (ordinateFiber D γ g) δ b ξ η := by sorry

theorem square_example_mixed_signs :
    (5 / 2 : ℝ) ≤ Real.cosh (-1) * Real.cosh 2 * Real.cosh 0 - 1 := by sorry

theorem square_example_empty {I : Type*} (δ : I → ℝ) (b ξ η : ℝ) :
    sameOrdinateCoshSum ∅ δ b ξ η = 0 ∧ horizontalSquareMass ∅ δ = 0 := by sorry

theorem square_example_singleton {I : Type*} (i : I) (δ : I → ℝ) (b : ℝ) :
    3 * b ^ 2 * (δ i) ^ 2 ≤ sameOrdinateCoshSum {i} δ b 1 1 := by sorry

theorem square_example_zero_scale {I : Type*} (D : Finset I) (δ : I → ℝ) (ξ η : ℝ) :
    sameOrdinateCoshSum D δ 0 ξ η = 0 := by sorry

theorem square_example_frequency_origin {I : Type*} (D : Finset I) (δ : I → ℝ) (b : ℝ) :
    sameOrdinateCoshSum D δ b 0 0 = 0 := by sorry

theorem square_example_frequency_axes (ξ η : ℝ) :
    horizontalFrequencyForm ξ 0 = ξ ^ 2 ∧ horizontalFrequencyForm 0 η = η ^ 2 ∧
      horizontalFrequencyForm ξ (-ξ) = ξ ^ 2 := by sorry

theorem square_example_repeated_occurrences (b ξ η : ℝ) :
    27 * b ^ 2 * horizontalFrequencyForm ξ η ≤
      sameOrdinateCoshSum Finset.univ (![1, 1, -1] : Fin 3 → ℝ) b ξ η := by sorry

theorem square_example_fiber_multiplicities :
    (ordinateFiber Finset.univ (![0, 0, 1] : Fin 3 → ℕ) 0).card = 2 ∧
    (ordinateFiber Finset.univ (![0, 0, 1] : Fin 3 → ℕ) 1).card = 1 := by sorry

end HigherCorrelations
