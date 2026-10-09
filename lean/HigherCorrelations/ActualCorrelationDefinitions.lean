import HigherCorrelations.ComplexFourierDefinitions
import HigherCorrelations.SummabilityDefinitions

/-! Actual zero-side correlation definitions. UNCONDITIONAL; all ordered occurrences. -/
namespace HigherCorrelations
noncomputable section

abbrev AnchorOccurrence (T : ℝ) := {i : ZeroOccurrence // T ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ 2 * T}
abbrev AnchoredTriple (T : ℝ) := AnchorOccurrence T × ZeroOccurrence × ZeroOccurrence

def anchoredRadius (T a : ℝ) (t : AnchoredTriple T) : ℝ :=
  max |a * (occurrenceOrdinate t.2.1 - occurrenceOrdinate t.1.val)|
      |a * (occurrenceOrdinate t.2.2 - occurrenceOrdinate t.1.val)|

def actualGaps (a : ℝ) (t : Fin 3 → ZeroOccurrence) : ℝ × ℝ :=
  (a * (occurrenceOrdinate (t 1) - occurrenceOrdinate (t 0)),
   a * (occurrenceOrdinate (t 2) - occurrenceOrdinate (t 0)))

def actualShifts (a : ℝ) (t : Fin 3 → ZeroOccurrence) : ℝ × ℝ :=
  (a * (occurrenceDisplacement (t 1) + occurrenceDisplacement (t 0)),
   a * (occurrenceDisplacement (t 2) + occurrenceDisplacement (t 0)))

def anchoredToTriple {T : ℝ} (t : AnchoredTriple T) : Fin 3 → ZeroOccurrence :=
  ![t.1.val, t.2.1, t.2.2]

def actualCorrelationTerm (a : ℝ) (w : ℝ → ℂ) (φ : ℝ × ℝ → ℂ)
    (complexArguments : Bool) (t : Fin 3 → ZeroOccurrence) : ℂ :=
  w (occurrenceOrdinate (t 0)) * complexFourier φ
    (complexPair (actualGaps a t) (if complexArguments then actualShifts a t else (0, 0)))

def meanSpacing (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi)) / (2 * Real.pi)

def dyadicIndex (r : ℝ) : ℕ :=
  (exists_nat_pow_near (show (1 : ℝ) ≤ 1 + max 0 r by linarith [le_max_left (0 : ℝ) r])
    (show (1 : ℝ) < 2 by norm_num)).choose


end
end HigherCorrelations
