import HigherCorrelations.FiniteDefinitions

/-! Definition-only vocabulary for the UNCONDITIONAL horizontal-square bound.
Every finite sum is over occurrence indices, including all repeated indices.
-/
namespace HigherCorrelations
noncomputable section

def horizontalCoshExcess (b ξ η d₀ d₁ d₂ : ℝ) : ℝ :=
  Real.cosh (b * d₀ * (ξ + η)) * Real.cosh (b * d₁ * ξ) *
    Real.cosh (b * d₂ * η) - 1

def horizontalSquareMass {I : Type*} (D : Finset I) (δ : I → ℝ) : ℝ :=
  ∑ i ∈ D, (δ i) ^ 2

def horizontalFrequencyForm (ξ η : ℝ) : ℝ := ξ ^ 2 + ξ * η + η ^ 2

def sameOrdinateCoshSum {I : Type*} (D : Finset I) (δ : I → ℝ) (b ξ η : ℝ) : ℝ :=
  ∑ i ∈ D, ∑ j ∈ D, ∑ k ∈ D, horizontalCoshExcess b ξ η (δ i) (δ j) (δ k)

def ordinateFiber {I A : Type*} [DecidableEq A] (D : Finset I) (γ : I → A) (g : A) : Finset I :=
  D.filter (fun i => γ i = g)

end
end HigherCorrelations
