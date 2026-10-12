import HigherCorrelations.LocalZeroCounting

/-! UNCONDITIONAL interval and cumulative counts, with absolute existential constants. -/
namespace HigherCorrelations
noncomputable section

theorem occurrence_interval_unit_cover (v w : ℝ) (_hvw : v ≤ w) :
    occurrenceInterval v w ⊆ (Finset.range (⌊w-v⌋₊+1)).biUnion
      (fun n => occurrenceInterval (v+n) (v+n+1)) := by
  classical
  intro i hi
  rcases (mem_occurrenceInterval v w i).mp hi with ⟨hl,hu⟩
  let n := ⌊occurrenceOrdinate i-v⌋₊
  have hn : (n:ℝ) ≤ occurrenceOrdinate i-v := Nat.floor_le (by linarith)
  have hn' : occurrenceOrdinate i-v < (n:ℝ)+1 := Nat.lt_floor_add_one _
  apply Finset.mem_biUnion.mpr
  refine ⟨n, Finset.mem_range.mpr (by dsimp [n]; exact Nat.lt_succ_of_le (Nat.floor_mono (by linarith))), ?_⟩
  exact (mem_occurrenceInterval _ _ i).mpr ⟨by linarith,by linarith⟩

theorem occurrence_count_interval :
    ∃ C : ℝ, 0 < C ∧ ∀ v w : ℝ, v ≤ w →
      ((occurrenceInterval v w).card : ℝ) ≤
        C*(w-v+1)*Real.log (max |v| |w|+2) := by
  classical
  obtain ⟨C,hC,hb⟩ := occurrence_count_local
  refine ⟨C,hC,fun v w hvw => ?_⟩
  let N := ⌊w-v⌋₊+1
  have hN : (N:ℝ) ≤ w-v+1 := by
    dsimp [N]; push_cast; linarith [Nat.floor_le (show 0 ≤ w-v by linarith)]
  have hlog : 0 ≤ Real.log (max |v| |w|+2) := Real.log_nonneg (by have := abs_nonneg v; have := le_max_left |v| |w|; linarith)
  have hcount : ((occurrenceInterval v w).card:ℝ) ≤
      ∑ n ∈ Finset.range N, ((occurrenceInterval (v+n) (v+n+1)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card (occurrence_interval_unit_cover v w hvw)).trans
      (Finset.card_biUnion_le)
  calc
    _ ≤ ∑ n ∈ Finset.range N, C*Real.log (max |v| |w|+2) := by
      apply hcount.trans
      apply Finset.sum_le_sum
      intro n hn
      have hn' : (n:ℝ) ≤ w-v := by
        have : n ≤ ⌊w-v⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
      have ha : |v+(n:ℝ)| ≤ max |v| |w| := abs_le.mpr
        ⟨by linarith [neg_abs_le v, le_max_left |v| |w|, Nat.cast_nonneg (α:=ℝ) n],
         by linarith [le_abs_self w,le_max_right |v| |w|]⟩
      exact (hb (v+n)).trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) (by linarith)) hC.le)
    _ = (N:ℝ)*(C*Real.log (max |v| |w|+2)) := by simp
    _ ≤ (w-v+1)*(C*Real.log (max |v| |w|+2)) := mul_le_mul_of_nonneg_right hN (mul_nonneg hC.le hlog)
    _ = _ := by ring

theorem occurrenceCutoff_eq_interval (U : ℝ) :
    occurrenceCutoff U = occurrenceInterval (-U) U := by
  ext i
  simp only [mem_occurrenceCutoff, mem_occurrenceInterval, abs_le]

theorem occurrence_count_logarithmic :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 0 ≤ U →
      ((occurrenceCutoff U).card : ℝ) ≤ C*(U+1)*Real.log (U+2) := by
  obtain ⟨C,hC,hb⟩ := occurrence_count_interval
  refine ⟨2*C, by positivity, fun U hU => ?_⟩
  have hh := hb (-U) U (by linarith)
  rw [← occurrenceCutoff_eq_interval] at hh
  simp only [abs_neg, abs_of_nonneg hU, max_self] at hh
  have hl : 0 ≤ Real.log (U+2) := Real.log_nonneg (by linarith)
  nlinarith [mul_nonneg hC.le hl]

theorem occurrence_count_centered :
    ∃ C : ℝ, 0 < C ∧ ∀ t r : ℝ, 0 ≤ r →
      ((occurrenceInterval (t-r) (t+r)).card:ℝ) ≤ C*(1+r)*Real.log (|t|+r+2) := by
  obtain ⟨C,hC,hb⟩ := occurrence_count_interval
  refine ⟨2*C,by positivity,fun t r hr => ?_⟩
  have hh := hb (t-r) (t+r) (by linarith)
  have hm : max |t-r| |t+r| ≤ |t|+r := max_le
    (by simpa [abs_of_nonneg hr] using abs_sub t r)
    (by simpa [abs_of_nonneg hr] using abs_add_le t r)
  have hl := Real.log_le_log (show 0 < max |t-r| |t+r|+2 by have := le_max_left |t-r| |t+r|; have := abs_nonneg (t-r); linarith)
    (show max |t-r| |t+r|+2 ≤ |t|+r+2 by linarith)
  have hp : 0 ≤ Real.log (|t|+r+2) := Real.log_nonneg (by have := abs_nonneg t; linarith)
  calc
    _ ≤ C*((t+r)-(t-r)+1)*Real.log (|t|+r+2) := hh.trans (mul_le_mul_of_nonneg_left hl (mul_nonneg hC.le (by linarith)))
    _ ≤ _ := by nlinarith [mul_nonneg hC.le hp]

end
end HigherCorrelations
