import HigherCorrelations.HorizontalSquareDefinitions

/-! Definition-only interfaces for UNCONDITIONAL analytic implications.
Shell bounds and summability are hypotheses, not asserted facts about zeta zeros.
All indices denote occurrences, with multiplicities retained.
-/
namespace HigherCorrelations
noncomputable section

/-- The ratio in the geometric shell majorant. -/
def dyadicRatio (d p : ℕ) : ℝ := (2 : ℝ) ^ d / (2 : ℝ) ^ p

/-- Finite shells partition occurrence indices via an explicit shell map. -/
structure OccurrenceShells (I : Type*) where
  shell : I → ℕ
  members : ℕ → Finset I
  mem_iff : ∀ i n, i ∈ members n ↔ shell i = n

/-- The real Fourier weight is paired with an already defined finite excess. -/
def integratedCoshExcess {I : Type*} (D : Finset I) (δ : I → ℝ)
    (b : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, φ z * sameOrdinateCoshSum D δ b z.1 z.2

/-- Frequency moment in the project's Fourier units. -/
def integratedFrequencyForm (φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, φ z * horizontalFrequencyForm z.1 z.2

/-- Moving mass: each row sums to one but every fixed coordinate tends to zero. -/
def movingSingleton (n i : ℕ) : ℝ := if i = n then 1 else 0

end
end HigherCorrelations
