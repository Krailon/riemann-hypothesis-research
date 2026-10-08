import HigherCorrelations.FiniteDefinitions
import HigherCorrelations.Definitions

/-! Specification only: intentional sorry terms; no solution imports this file. -/
namespace HigherCorrelations

theorem classifyTriple_iff {A : Type*} [DecidableEq A] (v : Fin 3 → A)
    (p : TriplePattern) : classifyTriple v = p ↔ HasPattern p v := by sorry

end HigherCorrelations
