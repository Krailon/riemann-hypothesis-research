import HigherCorrelations.HorizontalSquareDefinitions
import HigherCorrelations.FinitePatterns
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! UNCONDITIONAL real inequalities and finite same-ordinate sums.
The only infinite series used is mathlib's proved convergent scalar cosh series.
No infinite zero sum, Fourier integral, or quasi-RH import is used.
-/
namespace HigherCorrelations

theorem cosh_quadratic_lower (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hn (n : ℕ) : 0 ≤ x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
    apply div_nonneg
    · rw [pow_mul]
      exact pow_nonneg (sq_nonneg x) n
    · positivity
  have h := sum_le_hasSum (Finset.range 2) (fun n _ => hn n) (Real.hasSum_cosh x)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem cosh_triple_quadratic_lower (a₀ a₁ a₂ : ℝ) :
    (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2) / 2 ≤
      Real.cosh a₀ * Real.cosh a₁ * Real.cosh a₂ - 1 := by
  have hp : (1 + a₀ ^ 2 / 2) * (1 + a₁ ^ 2 / 2) * (1 + a₂ ^ 2 / 2) ≤
      Real.cosh a₀ * Real.cosh a₁ * Real.cosh a₂ := by
    gcongr <;> exact cosh_quadratic_lower _
  have h01 : 0 ≤ a₀ ^ 2 * a₁ ^ 2 := by positivity
  have h02 : 0 ≤ a₀ ^ 2 * a₂ ^ 2 := by positivity
  have h12 : 0 ≤ a₁ ^ 2 * a₂ ^ 2 := by positivity
  have h012 : 0 ≤ a₀ ^ 2 * a₁ ^ 2 * a₂ ^ 2 := by positivity
  nlinarith

theorem horizontal_cosh_square_lower (b ξ η d₀ d₁ d₂ : ℝ) :
    b ^ 2 / 2 * (d₀ ^ 2 * (ξ + η) ^ 2 + d₁ ^ 2 * ξ ^ 2 + d₂ ^ 2 * η ^ 2) ≤
      horizontalCoshExcess b ξ η d₀ d₁ d₂ := by
  have h := cosh_triple_quadratic_lower (b * d₀ * (ξ + η)) (b * d₁ * ξ) (b * d₂ * η)
  unfold horizontalCoshExcess
  convert h using 1; ring

theorem horizontal_frequency_lower (ξ η : ℝ) :
    (ξ ^ 2 + η ^ 2) / 2 ≤ horizontalFrequencyForm ξ η := by
  unfold horizontalFrequencyForm
  nlinarith [sq_nonneg (ξ + η)]

theorem horizontal_frequency_nonneg (ξ η : ℝ) : 0 ≤ horizontalFrequencyForm ξ η := by
  have h := horizontal_frequency_lower ξ η
  exact le_trans (by positivity) h

theorem horizontal_frequency_zero_iff (ξ η : ℝ) :
    horizontalFrequencyForm ξ η = 0 ↔ ξ = 0 ∧ η = 0 := by
  constructor
  · intro h
    have hl := horizontal_frequency_lower ξ η
    constructor <;> nlinarith [sq_nonneg ξ, sq_nonneg η]
  · rintro ⟨rfl, rfl⟩
    norm_num [horizontalFrequencyForm]

theorem horizontal_square_mass_nonneg {I : Type*} (D : Finset I) (δ : I → ℝ) :
    0 ≤ horizontalSquareMass D δ := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (δ i))

theorem horizontal_cube_square_sum {I : Type*} (D : Finset I) (δ : I → ℝ) (ξ η : ℝ) :
    (∑ i ∈ D, ∑ j ∈ D, ∑ k ∈ D,
      ((δ i) ^ 2 * (ξ + η) ^ 2 + (δ j) ^ 2 * ξ ^ 2 + (δ k) ^ 2 * η ^ 2)) =
      2 * (D.card : ℝ) ^ 2 * horizontalSquareMass D δ * horizontalFrequencyForm ξ η := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, horizontalSquareMass, horizontalFrequencyForm]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem same_ordinate_horizontal_square_lower {I : Type*}
    (D : Finset I) (δ : I → ℝ) (b ξ η : ℝ) :
    b ^ 2 * (D.card : ℝ) ^ 2 * horizontalSquareMass D δ * horizontalFrequencyForm ξ η ≤
      sameOrdinateCoshSum D δ b ξ η := by
  calc
    _ = ∑ i ∈ D, ∑ j ∈ D, ∑ k ∈ D,
        b ^ 2 / 2 * ((δ i) ^ 2 * (ξ + η) ^ 2 + (δ j) ^ 2 * ξ ^ 2 + (δ k) ^ 2 * η ^ 2) := by
      simp only [← Finset.mul_sum]
      rw [horizontal_cube_square_sum]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact horizontal_cosh_square_lower b ξ η (δ i) (δ j) (δ k)

theorem same_ordinate_cosh_nonneg {I : Type*}
    (D : Finset I) (δ : I → ℝ) (b ξ η : ℝ) : 0 ≤ sameOrdinateCoshSum D δ b ξ η := by
  have hQ := horizontal_square_mass_nonneg D δ
  have hP := horizontal_frequency_nonneg ξ η
  exact le_trans (by positivity : 0 ≤ b ^ 2 * (D.card : ℝ) ^ 2 *
    horizontalSquareMass D δ * horizontalFrequencyForm ξ η)
    (same_ordinate_horizontal_square_lower D δ b ξ η)

theorem weighted_ordinate_fibers_lower {I A : Type*} [DecidableEq A]
    (D : Finset I) (γ : I → A) (δ : I → ℝ) (W : A → ℝ)
    (hW : ∀ g ∈ D.image γ, 0 ≤ W g) (b ξ η : ℝ) :
    b ^ 2 * horizontalFrequencyForm ξ η *
      (∑ g ∈ D.image γ, W g * ((ordinateFiber D γ g).card : ℝ) ^ 2 *
        horizontalSquareMass (ordinateFiber D γ g) δ) ≤
      ∑ g ∈ D.image γ, W g * sameOrdinateCoshSum (ordinateFiber D γ g) δ b ξ η := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g hg
  have h := mul_le_mul_of_nonneg_left
    (same_ordinate_horizontal_square_lower (ordinateFiber D γ g) δ b ξ η) (hW g hg)
  convert h using 1; ring

end HigherCorrelations
