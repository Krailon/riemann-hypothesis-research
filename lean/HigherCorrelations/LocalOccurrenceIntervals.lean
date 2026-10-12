import HigherCorrelations.LocalZeroCountDefinitions
import HigherCorrelations.ZeroOccurrenceCounting
import HigherCorrelations.ZeroOccurrenceReflection

/-! UNCONDITIONAL closed occurrence intervals, endpoint membership and multiplicity sums. -/
namespace HigherCorrelations
noncomputable section

theorem stripZero_interval_finite (v w : ℝ) :
    Set.Finite {ρ : StripZero | v ≤ ρ.val.im ∧ ρ.val.im ≤ w} := by
  apply (stripZero_height_finite (max |v| |w|)).subset
  intro ρ hρ
  rcases hρ with ⟨hl,hu⟩
  change |ρ.val.im| ≤ max |v| |w|
  exact abs_le.mpr ⟨by linarith [neg_abs_le v, le_max_left |v| |w|],
    by linarith [le_abs_self w, le_max_right |v| |w|]⟩

theorem mem_stripZeroInterval (v w : ℝ) (ρ : StripZero) :
    ρ ∈ stripZeroInterval v w ↔ v ≤ ρ.val.im ∧ ρ.val.im ≤ w := by
  classical
  simp [stripZeroInterval, stripZero_interval_finite]

theorem mem_occurrenceInterval (v w : ℝ) (i : ZeroOccurrence) :
    i ∈ occurrenceInterval v w ↔ v ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ w := by
  classical
  simp [occurrenceInterval, mem_stripZeroInterval, occurrenceOrdinate, occurrenceValue]

theorem occurrenceInterval_card (v w : ℝ) :
    (occurrenceInterval v w).card = ∑ ρ ∈ stripZeroInterval v w, zeroMultiplicity ρ := by
  classical
  simp [occurrenceInterval, Finset.card_sigma]

theorem occurrenceInterval_subset_cutoff (v w : ℝ) :
    occurrenceInterval v w ⊆ occurrenceCutoff (max |v| |w|) := by
  intro i hi
  rcases (mem_occurrenceInterval v w i).mp hi with ⟨hl,hu⟩
  apply (mem_occurrenceCutoff _ _).mpr
  exact abs_le.mpr ⟨by linarith [neg_abs_le v, le_max_left |v| |w|],
    by linarith [le_abs_self w, le_max_right |v| |w|]⟩

theorem occurrenceInterval_mono {v w v' w' : ℝ} (hv : v' ≤ v) (hw : w ≤ w') :
    occurrenceInterval v w ⊆ occurrenceInterval v' w' := by
  intro i hi
  rcases (mem_occurrenceInterval v w i).mp hi with ⟨hl,hu⟩
  exact (mem_occurrenceInterval v' w' i).mpr ⟨hv.trans hl,hu.trans hw⟩

theorem occurrenceInterval_empty {v w : ℝ} (h : w < v) : occurrenceInterval v w = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rcases (mem_occurrenceInterval v w i).mp hi with ⟨hl,hu⟩
  linarith

theorem rightStripZeroInterval_mem (v w : ℝ) (ρ : StripZero) :
    ρ ∈ rightStripZeroInterval v w ↔ v ≤ ρ.val.im ∧ ρ.val.im ≤ w ∧ 1/2 ≤ ρ.val.re := by
  classical
  simp [rightStripZeroInterval, mem_stripZeroInterval, and_assoc]

theorem occurrenceInterval_card_le_twice_right (v w : ℝ) :
    (occurrenceInterval v w).card ≤ 2 * ∑ ρ ∈ rightStripZeroInterval v w, zeroMultiplicity ρ := by
  classical
  let A := (occurrenceInterval v w).filter (fun i => 1/2 ≤ (occurrenceValue i).re)
  let B := (occurrenceInterval v w).filter (fun i => ¬1/2 ≤ (occurrenceValue i).re)
  have hA : A = (rightStripZeroInterval v w).sigma (fun ρ => Finset.univ) := by
    ext i
    simp [A, occurrenceInterval, rightStripZeroInterval, occurrenceValue]
  have hB : B.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn occurrenceReflection
    · intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hi, hb⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_occurrenceInterval v w _).mpr
        rw [occurrenceReflection_ordinate]
        exact (mem_occurrenceInterval v w i).mp hi
      · have hh := occurrenceReflection_displacement i
        unfold occurrenceDisplacement at hh
        change 1/2 ≤ (occurrenceValue (occurrenceReflection i)).re
        linarith
    · exact occurrenceReflection_involutive.injective.injOn
  have he : A.card + B.card = (occurrenceInterval v w).card :=
    Finset.card_filter_add_card_filter_not _
  have hc : A.card = ∑ ρ ∈ rightStripZeroInterval v w, zeroMultiplicity ρ := by
    rw [hA]
    simp [Finset.card_sigma]
  omega

end
end HigherCorrelations
