import HigherCorrelations.ZeroReflection
import Mathlib.Analysis.Analytic.Order

/-! Definitions for actual nontrivial zero occurrences. Assumptions: UNCONDITIONAL.
An occurrence carries a multiplicity index; no simplicity or ordinate sign is imposed.
-/
namespace HigherCorrelations
noncomputable section

abbrev StripZero := {ρ : ℂ // IsCriticalStripZero ρ}

def zeroMultiplicity (ρ : StripZero) : ℕ := analyticOrderNatAt riemannZeta ρ.val

abbrev ZeroOccurrence := (ρ : StripZero) × Fin (zeroMultiplicity ρ)

def occurrenceValue (i : ZeroOccurrence) : ℂ := i.1.val

def occurrenceOrdinate (i : ZeroOccurrence) : ℝ := (occurrenceValue i).im

def occurrenceDisplacement (i : ZeroOccurrence) : ℝ := (occurrenceValue i).re - 1 / 2

/-- Inclusive height cutoff. The fallback is proved unreachable in ZeroOccurrences. -/
def occurrenceCutoff (U : ℝ) : Finset ZeroOccurrence := by
  classical
  exact if h : Set.Finite {i : ZeroOccurrence | |occurrenceOrdinate i| ≤ U}
    then h.toFinset else ∅

def stripZeroConjugate (ρ : StripZero) : StripZero :=
  ⟨starRingEnd ℂ ρ.val, by
    exact ⟨by simp [riemannZeta_conj, ρ.property.1], by simpa using ρ.property.2⟩⟩

def stripZeroOneSub (ρ : StripZero) : StripZero := ⟨1 - ρ.val, reflected_zero ρ.property⟩

def stripZeroHorizontalReflection (ρ : StripZero) : StripZero :=
  stripZeroOneSub (stripZeroConjugate ρ)

/-- The fallback is proved unreachable by multiplicity preservation. -/
def occurrenceReflection (i : ZeroOccurrence) : ZeroOccurrence := by
  classical
  exact if h : zeroMultiplicity (stripZeroHorizontalReflection i.1) = zeroMultiplicity i.1
    then ⟨stripZeroHorizontalReflection i.1, Fin.cast h.symm i.2⟩ else i


end
end HigherCorrelations
