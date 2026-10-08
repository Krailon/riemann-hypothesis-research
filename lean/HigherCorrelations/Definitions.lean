import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Project zero convention for the first formal milestone.

This predicate describes a zero in the open critical strip. It makes no
assertion about simplicity, the sign of the ordinate, or enumeration.
-/
namespace HigherCorrelations

def IsCriticalStripZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

def horizontalReflection (ρ : ℂ) : ℂ := 1 - starRingEnd ℂ ρ

end HigherCorrelations
