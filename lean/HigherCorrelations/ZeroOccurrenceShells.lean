import HigherCorrelations.ZeroOccurrenceCounting
import HigherCorrelations.OccurrenceSummability
import HigherCorrelations.ActualCorrelationDefinitions

/-! Dyadic shells for actual anchored occurrence triples. UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section

theorem anchor_finite (T : ℝ) : Finite (AnchorOccurrence T) := by
  apply Set.finite_coe_iff.mpr
  apply (occurrence_height_finite (2 * |T|)).subset
  intro i hi
  change T ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ 2 * T at hi
  change |occurrenceOrdinate i| ≤ 2 * |T|
  exact abs_le.mpr ⟨by linarith [hi.1, neg_abs_le T, abs_nonneg T], by linarith [hi.2, le_abs_self T]⟩

instance (T : ℝ) : Fintype (AnchorOccurrence T) := @Fintype.ofFinite _ (anchor_finite T)

theorem dyadicIndex_bounds (r : ℝ) (hr : 0 ≤ r) :
    (2 : ℝ) ^ dyadicIndex r ≤ 1 + r ∧ 1 + r < (2 : ℝ) ^ (dyadicIndex r + 1) := by
  have h := (exists_nat_pow_near (show (1 : ℝ) ≤ 1 + max 0 r by linarith [le_max_left (0 : ℝ) r])
    (show (1 : ℝ) < 2 by norm_num)).choose_spec
  change (2 : ℝ) ^ dyadicIndex r ≤ 1 + max 0 r ∧ 1 + max 0 r < (2 : ℝ) ^ (dyadicIndex r + 1) at h
  simpa only [max_eq_right hr] using h

theorem anchoredRadius_nonneg (T a : ℝ) (t : AnchoredTriple T) : 0 ≤ anchoredRadius T a t :=
  (abs_nonneg _).trans (le_max_left _ _)

private theorem partner_height_bound (T a R : ℝ) (ha : 0 < a) (t : AnchoredTriple T)
    (h : anchoredRadius T a t ≤ R) :
    |occurrenceOrdinate t.2.1| ≤ 2 * |T| + R / a ∧
    |occurrenceOrdinate t.2.2| ≤ 2 * |T| + R / a := by
  have hi : |occurrenceOrdinate t.1.val| ≤ 2 * |T| :=
    abs_le.mpr ⟨by linarith [t.1.property.1, neg_abs_le T, abs_nonneg T], by linarith [t.1.property.2, le_abs_self T]⟩
  have hh (i : ZeroOccurrence) (hb : |a * (occurrenceOrdinate i - occurrenceOrdinate t.1.val)| ≤ R) :
      |occurrenceOrdinate i| ≤ 2 * |T| + R / a := by
    rw [abs_mul, abs_of_pos ha] at hb
    have hd : |occurrenceOrdinate i - occurrenceOrdinate t.1.val| ≤ R / a :=
      (le_div_iff₀ ha).mpr (by linarith)
    calc
      _ ≤ |occurrenceOrdinate i - occurrenceOrdinate t.1.val| + |occurrenceOrdinate t.1.val| := by simpa using (abs_add_le (occurrenceOrdinate i - occurrenceOrdinate t.1.val) (occurrenceOrdinate t.1.val))
      _ ≤ _ := by linarith
  exact ⟨hh _ ((le_max_left _ _).trans h), hh _ ((le_max_right _ _).trans h)⟩

private theorem anchored_shell_finite (T a : ℝ) (ha : 0 < a) (n : ℕ) :
    Set.Finite {t : AnchoredTriple T | dyadicIndex (anchoredRadius T a t) = n} := by
  apply ((Set.finite_univ : (Set.univ : Set (AnchorOccurrence T)).Finite).prod
    ((occurrence_height_finite (2 * |T| + (2 : ℝ) ^ (n + 1) / a)).prod
      (occurrence_height_finite (2 * |T| + (2 : ℝ) ^ (n + 1) / a)))).subset
  intro t ht
  refine ⟨Set.mem_univ _, ?_⟩
  apply partner_height_bound T a _ ha t
  have hb := (dyadicIndex_bounds _ (anchoredRadius_nonneg T a t)).2
  change dyadicIndex (anchoredRadius T a t) = n at ht
  rw [ht] at hb
  linarith

def actualOccurrenceShells (T a : ℝ) (ha : 0 < a) : OccurrenceShells (AnchoredTriple T) where
  shell t := dyadicIndex (anchoredRadius T a t)
  members n := (anchored_shell_finite T a ha n).toFinset
  mem_iff _ _ := Set.Finite.mem_toFinset _

theorem actual_shell_radius_lower (T a : ℝ) (ha : 0 < a) (t : AnchoredTriple T) :
    (2 : ℝ) ^ (actualOccurrenceShells T a ha).shell t ≤ 1 + anchoredRadius T a t :=
  (dyadicIndex_bounds _ (anchoredRadius_nonneg T a t)).1

theorem actual_shell_count (T a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (((actualOccurrenceShells T a ha).members n).card : ℝ) ≤ C * ((2 : ℝ) ^ 4) ^ n := by
  classical
  obtain ⟨C, hC, hbound⟩ := occurrence_count_polynomial
  let K := 1 + 2 * |T| + 2 / a
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(Fintype.card (AnchorOccurrence T) : ℝ) * C ^ 2 * K ^ 4, by positivity, ?_⟩
  intro n
  let U := 2 * |T| + (2 : ℝ) ^ (n + 1) / a
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hsub : (actualOccurrenceShells T a ha).members n ⊆
      Finset.univ ×ˢ (occurrenceCutoff U ×ˢ occurrenceCutoff U) := by
    intro t ht
    have he := ((actualOccurrenceShells T a ha).mem_iff t n).mp ht
    have hb := (dyadicIndex_bounds _ (anchoredRadius_nonneg T a t)).2
    change dyadicIndex (anchoredRadius T a t) = n at he
    rw [he] at hb
    have hh := partner_height_bound T a ((2 : ℝ) ^ (n + 1)) ha t (by linarith)
    simpa only [Finset.mem_product, Finset.mem_univ, mem_occurrenceCutoff, true_and] using hh
  have hcard : (((actualOccurrenceShells T a ha).members n).card : ℝ) ≤
      (Fintype.card (AnchorOccurrence T) : ℝ) * ((occurrenceCutoff U).card : ℝ) ^ 2 := by
    exact_mod_cast (show ((actualOccurrenceShells T a ha).members n).card ≤
      Fintype.card (AnchorOccurrence T) * (occurrenceCutoff U).card ^ 2 by
        simpa [Finset.card_product, pow_two] using Finset.card_le_card hsub)
  have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hbase : 1 + U ≤ K * (2 : ℝ) ^ n := by
    dsimp [U, K]
    rw [pow_succ]
    have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 1 + 2 * |T| by positivity)
    ring_nf at hmul ⊢
    linarith
  calc
    _ ≤ (Fintype.card (AnchorOccurrence T) : ℝ) * (C * (1 + U) ^ 2) ^ 2 := by
      apply hcard.trans
      gcongr
      exact hbound U hU
    _ ≤ (Fintype.card (AnchorOccurrence T) : ℝ) * (C * (K * (2 : ℝ) ^ n) ^ 2) ^ 2 := by gcongr
    _ = _ := by rw [← pow_mul, Nat.mul_comm 4 n, pow_mul]; ring

theorem actual_shell_cardinality (T a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (Nat.card {t : AnchoredTriple T // dyadicIndex (anchoredRadius T a t) = n} : ℝ) ≤
      C * ((2 : ℝ) ^ 4) ^ n := by
  obtain ⟨C, hC, hb⟩ := actual_shell_count T a ha
  refine ⟨C, hC, ?_⟩
  intro n
  let := (anchored_shell_finite T a ha n).fintype
  let : Fintype {t : AnchoredTriple T // dyadicIndex (anchoredRadius T a t) = n} :=
    (anchored_shell_finite T a ha n).fintype
  have he := (anchored_shell_finite T a ha n).card_toFinset
  have hn : Nat.card {t : AnchoredTriple T // dyadicIndex (anchoredRadius T a t) = n} =
      ((actualOccurrenceShells T a ha).members n).card := by
    rw [Nat.card_eq_fintype_card]
    exact he.symm
  rw [hn]
  exact hb n

end
end HigherCorrelations
