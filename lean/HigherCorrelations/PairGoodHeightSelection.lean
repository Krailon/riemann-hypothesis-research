import HigherCorrelations.IntervalZeroCounting
import Mathlib.Data.Fintype.Card

/-! A finite, quantitative gap selection lemma for contour heights. UNCONDITIONAL.
The input finset can count occurrences, so repeated ordinates cause no difficulty. -/
namespace HigherCorrelations
noncomputable section

theorem finite_ordinate_gap {ι : Type*} (S : Finset ι) (ordinate : ι → ℝ) (H : ℝ) :
    ∃ U : ℝ, H < U ∧ U < H+1 ∧
      ∀ i ∈ S, 1/(4*(S.card+1:ℝ)) ≤ |U-ordinate i| := by
  classical
  let N : ℝ := S.card+1
  have hN : 0 < N := by dsimp [N]; positivity
  let sample : Fin (S.card+1) → ℝ := fun j => H + ((j:ℝ)+1/2)/N
  have hlo (j : Fin (S.card+1)) : H < sample j := by
    have hd : 0 < ((j:ℝ)+1/2)/N := by positivity
    dsimp [sample]
    linarith
  have hhi (j : Fin (S.card+1)) : sample j < H+1 := by
    have hj : (j:ℝ)+1/2 < N := by
      have h := j.isLt
      have hh : (j:ℝ) < (S.card+1:ℝ) := by exact_mod_cast h
      have hh' : (j:ℝ) ≤ (S.card:ℝ) := by exact_mod_cast (Nat.le_of_lt_succ h)
      dsimp [N]; linarith
    dsimp [sample]
    have hd := (div_lt_one hN).mpr hj
    linarith
  by_contra h
  push Not at h
  have hex (j : Fin (S.card+1)) : ∃ i : {i // i ∈ S},
      |sample j - ordinate i.val| < 1/(4*N) := by
    obtain ⟨i, hi, hdist⟩ := h (sample j) (hlo j) (hhi j)
    exact ⟨⟨i,hi⟩,hdist⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    have hdi := hf i
    have hdj := hf j
    rw [← hij] at hdj
    have ht := abs_sub_le (sample i) (ordinate (f i).val) (sample j)
    rw [abs_sub_comm (ordinate (f i).val) (sample j)] at ht
    have hb : |sample i-sample j| < 1/(2*N) := by
      have he : 1/(4*N)+1/(4*N) = 1/(2*N) := by ring
      linarith
    have he : sample i-sample j = ((i:ℝ)-(j:ℝ))/N := by dsimp [sample]; ring
    rw [he, abs_div, abs_of_pos hN] at hb
    have hdiff : |(i:ℝ)-(j:ℝ)| < 1 := by
      have hb' := (div_lt_iff₀ hN).mp hb
      have hn : 1/(2*N)*N = (1/2:ℝ) := by field_simp
      rw [hn] at hb'
      linarith
    apply Fin.ext
    have hab := abs_lt.mp hdiff
    have hij' : (i:ℝ) < (j:ℝ)+1 := by linarith
    have hji' : (j:ℝ) < (i:ℝ)+1 := by linarith
    have h1 : i.val < j.val+1 := by exact_mod_cast hij'
    have h2 : j.val < i.val+1 := by exact_mod_cast hji'
    omega
  have hc := Fintype.card_le_of_injective f hinj
  simp at hc

theorem pairGoodHeight_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 2 ≤ H →
      ∃ U : ℝ, H < U ∧ U < H+1 ∧
        ∀ i : ZeroOccurrence, 1/(C*Real.log (H+4)) ≤ |U-occurrenceOrdinate i| := by
  classical
  obtain ⟨A,hA,hcount⟩ := occurrence_count_interval
  let C : ℝ := 4*(4*A+1/Real.log 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun H hH => ?_⟩
  let S := occurrenceInterval (H-1) (H+2)
  have hlog : 0 < Real.log (H+4) := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log (H+4) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hS : (S.card:ℝ) ≤ 4*A*Real.log (H+4) := by
    have hb := hcount (H-1) (H+2) (by linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ H-1),
      abs_of_nonneg (by linarith : 0 ≤ H+2), max_eq_right (by linarith)] at hb
    convert hb using 1 <;> ring
  obtain ⟨U,hl,hu,hgap⟩ := finite_ordinate_gap S occurrenceOrdinate H
  refine ⟨U,hl,hu,fun i => ?_⟩
  have hden : 4*(S.card+1:ℝ) ≤ C*Real.log (H+4) := by
    have hb : 1 ≤ Real.log (H+4)/Real.log 2 := (one_le_div hl2).mpr hlog2
    dsimp [C]
    simp only [div_eq_mul_inv, one_mul] at hb ⊢
    nlinarith
  have hle : 1/(C*Real.log (H+4)) ≤ 1/(4*(S.card+1:ℝ)) :=
    one_div_le_one_div_of_le (by positivity) hden
  by_cases hi : i ∈ S
  · exact hle.trans (hgap i hi)
  · have hsmall : 1/(4*(S.card+1:ℝ)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α:=ℝ) S.card; linarith)
    apply hle.trans (hsmall.trans ?_)
    have hni : ¬ (H-1 ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ H+2) := by
      simpa only [S, mem_occurrenceInterval] using hi
    rcases not_and_or.mp hni with hlo | hhi
    · have hb := le_abs_self (U-occurrenceOrdinate i)
      linarith [lt_of_not_ge hlo]
    · have hb := neg_le_abs (U-occurrenceOrdinate i)
      linarith [lt_of_not_ge hhi]

theorem pairGoodHeight_gap_neg (U ε : ℝ)
    (hgap : ∀ i : ZeroOccurrence, ε ≤ |U-occurrenceOrdinate i|) :
    ∀ i : ZeroOccurrence, ε ≤ |-U-occurrenceOrdinate i| := by
  intro i
  let ρ := stripZeroConjugate i.1
  let j : ZeroOccurrence := ⟨ρ,⟨0,zeroMultiplicity_pos ρ⟩⟩
  have hb := hgap j
  have he : occurrenceOrdinate j = -occurrenceOrdinate i := by
    simp [j,ρ,stripZeroConjugate,occurrenceOrdinate,occurrenceValue]
  rw [he] at hb
  have hab : |-U-occurrenceOrdinate i| = |U-(-occurrenceOrdinate i)| := by
    rw [show -U-occurrenceOrdinate i = -(U-(-occurrenceOrdinate i)) by ring, abs_neg]
  rwa [hab]

theorem pairGoodHeight_sequence :
    ∃ (C : ℝ) (U : ℕ → ℝ), 0 < C ∧
      (∀ n : ℕ, (n:ℝ)+2 < U n ∧ U n < (n:ℝ)+3) ∧
      Filter.Tendsto U Filter.atTop Filter.atTop ∧
      ∀ (n : ℕ) (i : ZeroOccurrence),
        1/(C*Real.log ((n:ℝ)+6)) ≤ |U n-occurrenceOrdinate i| ∧
        1/(C*Real.log ((n:ℝ)+6)) ≤ |-U n-occurrenceOrdinate i| := by
  obtain ⟨C,hC,hgood⟩ := pairGoodHeight_exists
  have hex (n : ℕ) := hgood ((n:ℝ)+2) (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  choose U hlo hhi hgap using hex
  refine ⟨C,U,hC,fun n => ⟨hlo n,by linarith [hhi n]⟩,?_,?_⟩
  · apply Filter.tendsto_atTop_mono (f := fun n : ℕ => (n:ℝ)) (fun n => by linarith [hlo n])
    exact tendsto_natCast_atTop_atTop
  · intro n i
    constructor
    · convert hgap n i using 1 <;> ring
    · convert pairGoodHeight_gap_neg (U n) _ (hgap n) i using 1 <;> ring

end
end HigherCorrelations
