import HigherCorrelations.ActualCorrelationConvergence

/-! Actual occurrence regrouping and reflection after absolute convergence. UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open scoped ContDiff

theorem zero_occurrence_fiber_card (ρ : StripZero) :
    Nat.card {i : ZeroOccurrence // i.1 = ρ} = zeroMultiplicity ρ := by
  simpa using Nat.card_congr (Equiv.sigmaSubtype (β := fun z => Fin (zeroMultiplicity z)) ρ)

theorem actual_ordinate_regroup (f : ZeroOccurrence → ℂ)
    (hf : Summable (fun i => ‖f i‖)) :
    (∑' i, f i) = ∑' γ : ℝ, ∑' i : {i // occurrenceOrdinate i = γ}, f i :=
  tsum_regroup_occurrences occurrenceOrdinate f hf

theorem actual_triple_patterns (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    (∑' t, actualCorrelationTerm a w φ b t) = ∑ p : TriplePattern,
      ∑' t : {t // classifyTriple (occurrenceOrdinate ∘ t) = p}, actualCorrelationTerm a w φ b t := by
  classical
  exact tsum_triple_patterns occurrenceOrdinate _ (actual_summable_norm T a ha w hw φ hφ hc b)

theorem actual_eight_reflections (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    (∑' t, actualCorrelationTerm a w φ b t) = (1 / 8 : ℂ) *
      ∑ e : Fin 3 → Bool, ∑' t, actualCorrelationTerm a w φ b (reflectSlots occurrenceReflection e t) :=
  tsum_eight_reflections occurrenceReflection occurrenceReflection_involutive _
    (actual_summable_norm T a ha w hw φ hφ hc b)

theorem actual_signed_eight_reflections (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∑' t, (actualCorrelationTerm a w φ true t - actualCorrelationTerm a w φ false t)) =
      (1 / 8 : ℂ) * ∑ e : Fin 3 → Bool, ∑' t,
        (actualCorrelationTerm a w φ true (reflectSlots occurrenceReflection e t) -
         actualCorrelationTerm a w φ false (reflectSlots occurrenceReflection e t)) :=
  tsum_eight_reflections occurrenceReflection occurrenceReflection_involutive _
    (actual_signed_difference_summable T a ha w hw φ hφ hc)

theorem actual_reflection_preserves_patterns (e : Fin 3 → Bool) (t : Fin 3 → ZeroOccurrence) :
    classifyTriple (occurrenceOrdinate ∘ reflectSlots occurrenceReflection e t) =
      classifyTriple (occurrenceOrdinate ∘ t) := by
  classical
  exact reflectSlots_pattern occurrenceReflection occurrenceOrdinate occurrenceReflection_ordinate e t

theorem actual_cutoff_endpoint (i : ZeroOccurrence) : i ∈ occurrenceCutoff |occurrenceOrdinate i| :=
  (mem_occurrenceCutoff _ _).mpr le_rfl

theorem actual_reflection_cutoff (i : ZeroOccurrence) (U : ℝ) :
    occurrenceReflection i ∈ occurrenceCutoff U ↔ i ∈ occurrenceCutoff U := by
  rw [mem_occurrenceCutoff, mem_occurrenceCutoff, occurrenceReflection_ordinate]

theorem actual_zero_test (a : ℝ) (w : ℝ → ℂ) (b : Bool) (t : Fin 3 → ZeroOccurrence) :
    actualCorrelationTerm a w (fun _ => 0) b t = 0 := by
  simp [actualCorrelationTerm, complexFourier]

theorem complexPair_zero_band (x : ℝ × ℝ) : complexPair x (0, 0) = ((x.1 : ℂ), (x.2 : ℂ)) := by
  simp [complexPair]

end
end HigherCorrelations
