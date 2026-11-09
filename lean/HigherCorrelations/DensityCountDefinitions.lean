import HigherCorrelations.Zeta23Definitions

/-! Finite density counts on actual zero occurrences. No analytic density theorem is
assumed by these definitions. `UniformDyadicDensity` is an explicit hypothesis,
not an axiom or a proved instance. Horizontal thresholds are always strict. -/
namespace HigherCorrelations
noncomputable section

def rightDensityWindow (a b D : ℝ) : Finset ZeroOccurrence := by
  classical
  exact (occurrenceWindow a b).filter (fun i => D < occurrenceDisplacement i)

def leftDensityWindow (a b D : ℝ) : Finset ZeroOccurrence := by
  classical
  exact (occurrenceWindow a b).filter (fun i => occurrenceDisplacement i < -D)

def horizontalDensityWindow (a b D : ℝ) : Finset ZeroOccurrence := by
  classical
  exact (occurrenceWindow a b).filter (fun i => D < |occurrenceDisplacement i|)

def rightDensityInterval (a b D : ℝ) : Finset ZeroOccurrence := by
  classical
  exact (occurrenceInterval a b).filter (fun i => D < occurrenceDisplacement i)

def leftDensityInterval (a b D : ℝ) : Finset ZeroOccurrence := by
  classical
  exact (occurrenceInterval a b).filter (fun i => occurrenceDisplacement i < -D)

def horizontalDensityInterval (a b D : ℝ) : Finset ZeroOccurrence := by
  classical
  exact (occurrenceInterval a b).filter (fun i => D < |occurrenceDisplacement i|)

def rightDensityCount (σ V : ℝ) : ℕ := (rightDensityWindow 0 V (σ-1/2)).card

def densityScaledTail (T v : ℝ) : ℕ :=
  (horizontalDensityInterval (T/2) (5*T/2) (v/Real.log T)).card

structure UniformDyadicDensity (C T₀ : ℝ) : Prop where
  constant_pos : 0 < C
  threshold_ge_three : 3 ≤ T₀
  bound : ∀ V D : ℝ, T₀ ≤ V → 0 ≤ D → D ≤ 331/1000 →
    ((rightDensityWindow V (2*V) D).card : ℝ) ≤
      C*(V^(1-D/4)*Real.log V+(Real.log V)^2)

end
end HigherCorrelations
