import HigherCorrelations.Zeta23Definitions
import HigherCorrelations.IntervalZeroCounting
import Zeta23.RvM.Statement
import Zeta23.GammaFacts.Complete

/-! UNCONDITIONAL dyadic Riemann–von Mangoldt with analytic multiplicities.
All heights are real; endpoint ordinates need not be zero-free.
Constants and the sufficiently-large threshold are existential. -/
namespace HigherCorrelations
noncomputable section

theorem mem_occurrenceWindow (a b : ℝ) (i : ZeroOccurrence) :
    i ∈ occurrenceWindow a b ↔ a < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b := by
  classical
  simp only [occurrenceWindow, Finset.mem_filter, mem_occurrenceInterval]
  constructor
  · rintro ⟨⟨_, hb⟩, ha⟩; exact ⟨ha,hb⟩
  · rintro ⟨ha,hb⟩; exact ⟨⟨ha.le,hb⟩,ha⟩

theorem occurrenceWindow_empty (a b : ℝ) (h : b ≤ a) : occurrenceWindow a b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rcases (mem_occurrenceWindow a b i).mp hi with ⟨ha,hb⟩
  exact (not_lt_of_ge (hb.trans h)) ha

theorem occurrenceInterval_card_split (a b : ℝ) (hab : a ≤ b) :
    (occurrenceInterval a b).card = (occurrenceWindow a b).card +
      (occurrenceInterval a a).card := by
  classical
  have he : (occurrenceInterval a b).filter (fun i => ¬ a < occurrenceOrdinate i) =
      occurrenceInterval a a := by
    ext i
    simp only [Finset.mem_filter, mem_occurrenceInterval, not_lt]
    constructor
    · rintro ⟨⟨ha,_⟩,hb⟩; exact ⟨ha,hb⟩
    · rintro ⟨ha,hb⟩; exact ⟨⟨ha,hb.trans hab⟩,hb⟩
  simpa only [occurrenceWindow, he] using
    (Finset.card_filter_add_card_filter_not (s := occurrenceInterval a b)
      (fun i => a < occurrenceOrdinate i)).symm

theorem occurrenceWindow_card_eq_zeta23 (a b : ℝ) :
    (occurrenceWindow a b).card = Zeta23.Ncount a b := by
  classical
  let s := (stripZeroInterval a b).filter (fun ρ => a < ρ.val.im)
  have hs (ρ : StripZero) : ρ ∈ s ↔ a < ρ.val.im ∧ ρ.val.im ≤ b := by
    simp only [s, Finset.mem_filter, mem_stripZeroInterval]
    constructor
    · rintro ⟨⟨_,hb⟩,ha⟩; exact ⟨ha,hb⟩
    · rintro ⟨ha,hb⟩; exact ⟨⟨ha.le,hb⟩,ha⟩
  have hw : occurrenceWindow a b = s.sigma (fun ρ => Finset.univ) := by
    ext i
    simp [mem_occurrenceWindow, Finset.mem_sigma, hs, occurrenceOrdinate, occurrenceValue]
  rw [hw, Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite a b)]
  refine Finset.sum_bij (fun ρ _ => ρ.val) ?_ ?_ ?_ ?_
  · intro ρ hρ
    exact (Zeta23.zerosIn_finite a b).mem_toFinset.mpr ⟨ρ.property, hs ρ |>.mp hρ⟩
  · intro ρ hρ τ hτ he
    exact Subtype.ext he
  · intro ρ hρ
    have hh := (Zeta23.zerosIn_finite a b).mem_toFinset.mp hρ
    exact ⟨⟨ρ,hh.1⟩,(hs _).mpr hh.2,rfl⟩
  · intro ρ _
    rfl

theorem zeta23_dyadic_occurrences :
    ∃ C T₀ : ℝ, 0 < C ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |((occurrenceWindow T (2*T)).card : ℝ) - zetaDyadicMain T| ≤ C * Real.log T := by
  obtain ⟨C,T₀,h⟩ := (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts).main
  refine ⟨|C|+1,max T₀ 3,by positivity,le_max_right _ _,fun T hT => ?_⟩
  have hT3 : 3 ≤ T := (le_max_right _ _).trans hT
  have hh := h T ((le_max_left _ _).trans hT)
  rw [occurrenceWindow_card_eq_zeta23]
  have he : Zeta23.zetaZeroConfig.N T (2*T) = Zeta23.Ncount T (2*T) := rfl
  rw [he] at hh
  change |(Zeta23.Ncount T (2*T) : ℝ) - zetaDyadicMain T| ≤ C * Real.log T at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C])
    (Real.log_nonneg (by linarith)))

theorem zeta23_dyadic_closed_occurrences :
    ∃ C T₀ : ℝ, 0 < C ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |((occurrenceInterval T (2*T)).card : ℝ) - zetaDyadicMain T| ≤ C * Real.log T := by
  obtain ⟨C,T₀,hC,hT₀,h⟩ := zeta23_dyadic_occurrences
  obtain ⟨A,hA,ha⟩ := occurrence_count_local
  refine ⟨C+2*A,T₀,by positivity,hT₀,fun T hT => ?_⟩
  have ht : 3 ≤ T := hT₀.trans hT
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hatom : ((occurrenceInterval T T).card : ℝ) ≤ 2*A*Real.log T := by
    have hs := Finset.card_le_card (occurrenceInterval_mono (v:=T) (w:=T)
      (v':=T) (w':=T+1) le_rfl (by linarith))
    have hh := ha T
    rw [abs_of_nonneg (by linarith : 0 ≤ T)] at hh
    have hl : Real.log (T+2) ≤ 2*Real.log T := by
      calc
        _ ≤ Real.log (T*T) := Real.log_le_log (by linarith) (by nlinarith)
        _ = _ := by rw [Real.log_mul (by linarith) (by linarith)]; ring
    exact (show ((occurrenceInterval T T).card : ℝ) ≤
      ((occurrenceInterval T (T+1)).card : ℝ) by exact_mod_cast hs).trans
      (hh.trans (by nlinarith))
  rw [occurrenceInterval_card_split T (2*T) (by linarith), Nat.cast_add]
  calc
    _ ≤ |((occurrenceWindow T (2*T)).card : ℝ) - zetaDyadicMain T| +
        ((occurrenceInterval T T).card : ℝ) := by
      simpa only [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (occurrenceInterval T T).card),
        add_sub_right_comm] using abs_add_le
          (((occurrenceWindow T (2*T)).card : ℝ) - zetaDyadicMain T)
          ((occurrenceInterval T T).card : ℝ)
    _ ≤ _ := by nlinarith [h T hT]

end
end HigherCorrelations
