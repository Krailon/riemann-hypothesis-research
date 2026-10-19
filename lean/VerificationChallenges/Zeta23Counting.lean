import HigherCorrelations.Zeta23Definitions

namespace HigherCorrelations
noncomputable section
open scoped ComplexOrder

theorem mem_occurrenceWindow (a b : ℝ) (i : ZeroOccurrence) :
    i ∈ occurrenceWindow a b ↔ a < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b := by sorry

theorem occurrenceWindow_empty (a b : ℝ) (h : b ≤ a) : occurrenceWindow a b = ∅ := by sorry

theorem occurrenceInterval_card_split (a b : ℝ) (hab : a ≤ b) :
    (occurrenceInterval a b).card = (occurrenceWindow a b).card +
      (occurrenceInterval a a).card := by sorry

theorem zeta23_dyadic_occurrences :
    ∃ C T₀ : ℝ, 0 < C ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |((occurrenceWindow T (2*T)).card : ℝ) - zetaDyadicMain T| ≤ C * Real.log T := by sorry

theorem zeta23_dyadic_closed_occurrences :
    ∃ C T₀ : ℝ, 0 < C ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |((occurrenceInterval T (2*T)).card : ℝ) - zetaDyadicMain T| ≤ C * Real.log T := by sorry

end
end HigherCorrelations
