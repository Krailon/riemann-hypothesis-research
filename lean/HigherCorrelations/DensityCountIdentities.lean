import HigherCorrelations.DensityCountDefinitions
import HigherCorrelations.Zeta23Counting

/-! UNCONDITIONAL finite counting and multiplicity-preserving reflection.
These identities neither use nor establish `UniformDyadicDensity`. -/
namespace HigherCorrelations
noncomputable section
open scoped Classical

theorem mem_rightDensityWindow (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ rightDensityWindow a b D ↔
      a < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ D < occurrenceDisplacement i := by
  simp [rightDensityWindow, mem_occurrenceWindow, and_assoc]

theorem mem_leftDensityWindow (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ leftDensityWindow a b D ↔
      a < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ occurrenceDisplacement i < -D := by
  simp [leftDensityWindow, mem_occurrenceWindow, and_assoc]

theorem mem_horizontalDensityWindow (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ horizontalDensityWindow a b D ↔
      a < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ D < |occurrenceDisplacement i| := by
  simp [horizontalDensityWindow, mem_occurrenceWindow, and_assoc]

theorem mem_rightDensityInterval (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ rightDensityInterval a b D ↔
      a ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ D < occurrenceDisplacement i := by
  simp [rightDensityInterval, mem_occurrenceInterval, and_assoc]

theorem mem_leftDensityInterval (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ leftDensityInterval a b D ↔
      a ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ occurrenceDisplacement i < -D := by
  simp [leftDensityInterval, mem_occurrenceInterval, and_assoc]

theorem mem_horizontalDensityInterval (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ horizontalDensityInterval a b D ↔
      a ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ D < |occurrenceDisplacement i| := by
  simp [horizontalDensityInterval, mem_occurrenceInterval, and_assoc]

theorem rightDensityWindow_empty (a b D : ℝ) (h : b ≤ a) : rightDensityWindow a b D = ∅ := by
  simp [rightDensityWindow, occurrenceWindow_empty a b h]

theorem horizontalDensityWindow_empty (a b D : ℝ) (h : b ≤ a) :
    horizontalDensityWindow a b D = ∅ := by
  simp [horizontalDensityWindow, occurrenceWindow_empty a b h]

theorem horizontalDensityInterval_empty (a b D : ℝ) (h : b < a) :
    horizontalDensityInterval a b D = ∅ := by
  simp [horizontalDensityInterval, occurrenceInterval_empty h]

theorem rightDensityWindow_mono {a b D a' b' D' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') (hD : D' ≤ D) :
    rightDensityWindow a b D ⊆ rightDensityWindow a' b' D' := by
  intro i hi
  rcases (mem_rightDensityWindow _ _ _ _).mp hi with ⟨hl,hu,hd⟩
  exact (mem_rightDensityWindow _ _ _ _).mpr ⟨ha.trans_lt hl,hu.trans hb,hD.trans_lt hd⟩

theorem horizontalDensityInterval_mono {a b D a' b' D' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') (hD : D' ≤ D) :
    horizontalDensityInterval a b D ⊆ horizontalDensityInterval a' b' D' := by
  intro i hi
  rcases (mem_horizontalDensityInterval _ _ _ _).mp hi with ⟨hl,hu,hd⟩
  exact (mem_horizontalDensityInterval _ _ _ _).mpr ⟨ha.trans hl,hu.trans hb,hD.trans_lt hd⟩

theorem rightDensityWindow_card (a b D : ℝ) :
    (rightDensityWindow a b D).card =
      ∑ ρ ∈ (stripZeroInterval a b).filter (fun ρ => a < ρ.val.im ∧ D < ρ.val.re-1/2),
        zeroMultiplicity ρ := by
  have he : rightDensityWindow a b D =
      ((stripZeroInterval a b).filter (fun ρ => a < ρ.val.im ∧ D < ρ.val.re-1/2)).sigma
        (fun _ => Finset.univ) := by
    ext i
    simp only [mem_rightDensityWindow, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_univ, and_true, mem_stripZeroInterval]
    dsimp [occurrenceOrdinate, occurrenceDisplacement, occurrenceValue]
    constructor
    · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1.le,h2⟩,h1,h3⟩
    · rintro ⟨⟨_,h2⟩,h1,h3⟩; exact ⟨h1,h2,h3⟩
  rw [he, Finset.card_sigma]
  simp

theorem horizontalDensityInterval_card (a b D : ℝ) :
    (horizontalDensityInterval a b D).card =
      ∑ ρ ∈ (stripZeroInterval a b).filter (fun ρ => D < |ρ.val.re-1/2|),
        zeroMultiplicity ρ := by
  have he : horizontalDensityInterval a b D =
      ((stripZeroInterval a b).filter (fun ρ => D < |ρ.val.re-1/2|)).sigma
        (fun _ => Finset.univ) := by
    ext i
    simp [horizontalDensityInterval, occurrenceInterval, occurrenceDisplacement, occurrenceValue]
  rw [he, Finset.card_sigma]
  simp

private theorem filtered_endpoint_split (a b : ℝ) (hab : a ≤ b) (p : ZeroOccurrence → Prop) :
    ((occurrenceInterval a b).filter p).card = ((occurrenceWindow a b).filter p).card +
      ((occurrenceInterval a a).filter p).card := by
  have he : (occurrenceInterval a b).filter p =
      ((occurrenceWindow a b).filter p) ∪ ((occurrenceInterval a a).filter p) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, mem_occurrenceInterval, mem_occurrenceWindow]
    constructor
    · rintro ⟨⟨hl,hu⟩,hp⟩
      rcases hl.eq_or_lt with he | hh
      · exact Or.inr ⟨⟨hl,he ▸ le_rfl⟩,hp⟩
      · exact Or.inl ⟨⟨hh,hu⟩,hp⟩
    · rintro (⟨⟨hl,hu⟩,hp⟩ | ⟨⟨hl,hu⟩,hp⟩)
      · exact ⟨⟨hl.le,hu⟩,hp⟩
      · exact ⟨⟨hl,hu.trans hab⟩,hp⟩
  rw [he, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi := (mem_occurrenceWindow _ _ _).mp (Finset.mem_filter.mp hi).1
  have hj := (mem_occurrenceInterval _ _ _).mp (Finset.mem_filter.mp hj).1
  exact (not_lt_of_ge hj.2) hi.1

theorem rightDensityInterval_endpoint (a b D : ℝ) (hab : a ≤ b) :
    (rightDensityInterval a b D).card = (rightDensityWindow a b D).card +
      (rightDensityInterval a a D).card :=
  filtered_endpoint_split a b hab _

theorem horizontalDensityInterval_endpoint (a b D : ℝ) (hab : a ≤ b) :
    (horizontalDensityInterval a b D).card = (horizontalDensityWindow a b D).card +
      (horizontalDensityInterval a a D).card :=
  filtered_endpoint_split a b hab _

theorem rightDensityCount_split (σ a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    rightDensityCount σ b = rightDensityCount σ a + (rightDensityWindow a b (σ-1/2)).card := by
  have he : rightDensityWindow 0 b (σ-1/2) =
      rightDensityWindow 0 a (σ-1/2) ∪ rightDensityWindow a b (σ-1/2) := by
    ext i
    simp only [mem_rightDensityWindow, Finset.mem_union]
    constructor
    · rintro ⟨hl,hu,hd⟩
      by_cases h : occurrenceOrdinate i ≤ a
      · exact Or.inl ⟨hl,h,hd⟩
      · exact Or.inr ⟨lt_of_not_ge h,hu,hd⟩
    · rintro (⟨hl,hu,hd⟩ | ⟨hl,hu,hd⟩)
      · exact ⟨hl,hu.trans hab,hd⟩
      · exact ⟨ha.trans_lt hl,hu,hd⟩
  unfold rightDensityCount
  rw [he, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi := (mem_rightDensityWindow _ _ _ _).mp hi
  have hj := (mem_rightDensityWindow _ _ _ _).mp hj
  exact (not_lt_of_ge hi.2.1) hj.1

theorem rightDensityCount_difference (σ a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    rightDensityCount σ b - rightDensityCount σ a = (rightDensityWindow a b (σ-1/2)).card := by
  rw [rightDensityCount_split σ a b ha hab, Nat.add_sub_cancel_left]

private theorem reflected_filter_card (S : Finset ZeroOccurrence)
    (hS : ∀ i, occurrenceReflection i ∈ S ↔ i ∈ S) (D : ℝ) :
    (S.filter (fun i => occurrenceDisplacement i < -D)).card =
      (S.filter (fun i => D < occurrenceDisplacement i)).card := by
  apply Finset.card_bij (fun i _ => occurrenceReflection i)
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi,hd⟩
    exact Finset.mem_filter.mpr ⟨(hS i).mpr hi,by rw [occurrenceReflection_displacement]; linarith⟩
  · intro i hi j hj he
    exact occurrenceReflection_involutive.injective he
  · intro j hj
    refine ⟨occurrenceReflection j,?_,occurrenceReflection_involutive j⟩
    rcases Finset.mem_filter.mp hj with ⟨hj,hd⟩
    exact Finset.mem_filter.mpr ⟨(hS j).mpr hj,by rw [occurrenceReflection_displacement]; linarith⟩

theorem densityWindow_reflection (a b D : ℝ) :
    (leftDensityWindow a b D).card = (rightDensityWindow a b D).card := by
  apply reflected_filter_card
  intro i
  simp [mem_occurrenceWindow, occurrenceReflection_ordinate]

theorem densityInterval_reflection (a b D : ℝ) :
    (leftDensityInterval a b D).card = (rightDensityInterval a b D).card := by
  apply reflected_filter_card
  intro i
  simp [mem_occurrenceInterval, occurrenceReflection_ordinate]

private theorem abs_filter_card (S : Finset ZeroOccurrence) (D : ℝ) (hD : 0 ≤ D) :
    (S.filter (fun i => D < |occurrenceDisplacement i|)).card =
      (S.filter (fun i => occurrenceDisplacement i < -D)).card +
      (S.filter (fun i => D < occurrenceDisplacement i)).card := by
  have he : S.filter (fun i => D < |occurrenceDisplacement i|) =
      S.filter (fun i => occurrenceDisplacement i < -D) ∪ S.filter (fun i => D < occurrenceDisplacement i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, lt_abs]
    constructor
    · rintro ⟨hi, hd | hd⟩
      · exact Or.inr ⟨hi,hd⟩
      · exact Or.inl ⟨hi,by linarith⟩
    · rintro (⟨hi,hd⟩ | ⟨hi,hd⟩)
      · exact ⟨hi,Or.inr (by linarith)⟩
      · exact ⟨hi,Or.inl hd⟩
  rw [he, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi := (Finset.mem_filter.mp hi).2
  have hj := (Finset.mem_filter.mp hj).2
  linarith

theorem horizontalDensityWindow_twice_right (a b D : ℝ) (hD : 0 ≤ D) :
    (horizontalDensityWindow a b D).card = 2*(rightDensityWindow a b D).card := by
  have h := abs_filter_card (occurrenceWindow a b) D hD
  change (horizontalDensityWindow a b D).card =
    (leftDensityWindow a b D).card+(rightDensityWindow a b D).card at h
  rw [densityWindow_reflection] at h
  omega

theorem horizontalDensityInterval_twice_right (a b D : ℝ) (hD : 0 ≤ D) :
    (horizontalDensityInterval a b D).card = 2*(rightDensityInterval a b D).card := by
  have h := abs_filter_card (occurrenceInterval a b) D hD
  change (horizontalDensityInterval a b D).card =
    (leftDensityInterval a b D).card+(rightDensityInterval a b D).card at h
  rw [densityInterval_reflection] at h
  omega

theorem horizontalDensityInterval_excludes_boundary (a b D : ℝ) (i : ZeroOccurrence)
    (hi : |occurrenceDisplacement i| = D) : i ∉ horizontalDensityInterval a b D := by
  simp [mem_horizontalDensityInterval, hi]

theorem horizontalDensityInterval_excludes_line (a b : ℝ) (i : ZeroOccurrence)
    (hi : occurrenceDisplacement i = 0) : i ∉ horizontalDensityInterval a b 0 := by
  apply horizontalDensityInterval_excludes_boundary
  simp [hi]

theorem leftDensityWindow_empty (a b D : ℝ) (h : b ≤ a) : leftDensityWindow a b D = ∅ := by
  simp [leftDensityWindow, occurrenceWindow_empty a b h]

theorem rightDensityInterval_empty (a b D : ℝ) (h : b < a) : rightDensityInterval a b D = ∅ := by
  simp [rightDensityInterval, occurrenceInterval_empty h]

theorem leftDensityInterval_empty (a b D : ℝ) (h : b < a) : leftDensityInterval a b D = ∅ := by
  simp [leftDensityInterval, occurrenceInterval_empty h]

theorem mem_horizontalDensityInterval_singleton (a D : ℝ) (i : ZeroOccurrence) :
    i ∈ horizontalDensityInterval a a D ↔
      occurrenceOrdinate i = a ∧ D < |occurrenceDisplacement i| := by
  rw [mem_horizontalDensityInterval]
  constructor
  · rintro ⟨hl,hu,hd⟩; exact ⟨le_antisymm hu hl,hd⟩
  · rintro ⟨he,hd⟩; exact ⟨he.ge,he.le,hd⟩

theorem rightDensityCount_card (σ V : ℝ) :
    rightDensityCount σ V =
      ∑ ρ ∈ (stripZeroInterval 0 V).filter (fun ρ => 0 < ρ.val.im ∧ σ < ρ.val.re),
        zeroMultiplicity ρ := by
  unfold rightDensityCount
  rw [rightDensityWindow_card]
  congr 1
  ext ρ
  simp only [Finset.mem_filter]
  constructor <;> rintro ⟨h,hγ,hβ⟩ <;> exact ⟨h,hγ,by linarith⟩

end
end HigherCorrelations
