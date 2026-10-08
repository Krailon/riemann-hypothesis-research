import Mathlib

/-! Definition-only vocabulary for UNCONDITIONAL finite occurrence bookkeeping.
Slots 0,1,2 correspond to manuscript slots 1,2,3. A label map need not be injective.
-/
namespace HigherCorrelations

inductive TriplePattern
  | allEqual | only01 | only02 | only12 | allDistinct
  deriving DecidableEq, Repr

instance : Fintype TriplePattern :=
  ⟨{.allEqual, .only01, .only02, .only12, .allDistinct}, by intro p; cases p <;> simp⟩

def HasPattern {A : Type*} (p : TriplePattern) (v : Fin 3 → A) : Prop :=
  match p with
  | .allEqual => v 0 = v 1 ∧ v 1 = v 2
  | .only01 => v 0 = v 1 ∧ v 0 ≠ v 2
  | .only02 => v 0 = v 2 ∧ v 0 ≠ v 1
  | .only12 => v 1 = v 2 ∧ v 0 ≠ v 1
  | .allDistinct => v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2

def classifyTriple {A : Type*} [DecidableEq A] (v : Fin 3 → A) : TriplePattern :=
  if v 0 = v 1 then (if v 1 = v 2 then .allEqual else .only01)
  else if v 0 = v 2 then .only02
  else if v 1 = v 2 then .only12 else .allDistinct

def tripleDomain {I : Type*} (S : Fin 3 → Finset I) : Finset (Fin 3 → I) :=
  Fintype.piFinset S

def patternDomain {I A : Type*} [DecidableEq A] (q : I → A)
    (S : Fin 3 → Finset I) (p : TriplePattern) : Finset (Fin 3 → I) :=
  (tripleDomain S).filter (fun t => classifyTriple (q ∘ t) = p)

def reflectSlots {I : Type*} (r : I → I) (e : Fin 3 → Bool)
    (t : Fin 3 → I) : Fin 3 → I := fun j => if e j then r (t j) else t j

def reflectionSign (b : Bool) : ℂ := if b then -1 else 1

def signCharacter (s : Finset (Fin 3)) (e : Fin 3 → Bool) : ℂ :=
  ∏ j ∈ s, reflectionSign (e j)

noncomputable def signCoefficient (K : (Fin 3 → Bool) → ℂ) (s : Finset (Fin 3)) : ℂ :=
  (1 / 8 : ℂ) * ∑ e, signCharacter s e * K e

end HigherCorrelations
