import HigherCorrelations.KernelTailBounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-! UNCONDITIONAL finite first-moment bounds with absolute inherited counting
constants. Closed occurrence intervals preserve all endpoint multiplicities. -/
namespace HigherCorrelations
noncomputable section
open Set

theorem localization_log_ge_one (T : ℝ) (hT : 3≤T) : 1≤Real.log (2*T+2) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<(2:ℝ)^2)
    (by nlinarith : (2:ℝ)^2 ≤ 2*T+2)
  rw [Real.log_pow] at hh
  norm_num at h hh
  linarith

theorem localization_local_log (T x : ℝ) (hT : 3≤T) (hx : |x|≤4*T+2) :
    Real.log (|x|+2) ≤ 2*Real.log (2*T+2) := by
  have h := Real.log_le_log (by positivity : 0 < |x|+2)
    (by nlinarith [sq_nonneg T] : |x|+2 ≤ (2*T+2)^2)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem localization_unit_shell_weight (u : ℝ) (n : ℕ) (hn : (n:ℝ)≤|u|) :
    |u| *ordinateKernel u ≤ 2/((n:ℝ)+1) := by
  have hu := ordinateKernel_quadratic u
  have hp : 0<1+|u| := by positivity
  calc
    _ ≤ |u| *(2/(1+|u|)^2) := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    _ ≤ 2/(1+|u|) := by
      apply (le_div_iff₀ hp).mpr
      field_simp
      nlinarith [abs_nonneg u]
    _ ≤ 2/((n:ℝ)+1) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

private theorem unit_shell_cover (t : ℝ) (n : ℕ) (i : ZeroOccurrence)
    (hn : ⌊|t-occurrenceOrdinate i|⌋₊=n) :
    i ∈ occurrenceInterval (t-(n:ℝ)-1) (t-(n:ℝ)) ∪
      occurrenceInterval (t+n) (t+n+1) := by
  have hl := Nat.floor_le (abs_nonneg (t-occurrenceOrdinate i))
  have hu := Nat.lt_floor_add_one |t-occurrenceOrdinate i|
  rw [hn] at hl hu
  apply Finset.mem_union.mpr
  by_cases ht : 0≤t-occurrenceOrdinate i
  · rw [abs_of_nonneg ht] at hl hu
    exact Or.inl ((mem_occurrenceInterval _ _ _).mpr ⟨by linarith,by linarith⟩)
  · rw [abs_of_neg (lt_of_not_ge ht)] at hl hu
    exact Or.inr ((mem_occurrenceInterval _ _ _).mpr ⟨by linarith,by linarith⟩)

theorem localization_near_moment_finite :
    ∃ C : ℝ, 0<C ∧ ∀ T t : ℝ, 3≤T → t ∈ Icc 0 (3*T) →
      ∀ s : Finset ZeroOccurrence, (∀ i ∈ s, |t-occurrenceOrdinate i|≤T) →
      (∑ i ∈ s, |t-occurrenceOrdinate i| *ordinateKernel (t-occurrenceOrdinate i)) ≤
        C*Real.log (2*T+2)^2 := by
  classical
  obtain ⟨C,hC,hcount⟩ := occurrence_count_local
  refine ⟨16*C,by positivity,fun T t hT ht s hs => ?_⟩
  let N := ⌊T⌋₊+1
  have hN : (N:ℝ)≤T+1 := by
    dsimp [N]; push_cast; linarith [Nat.floor_le (by linarith : 0≤T)]
  have hn (i : ZeroOccurrence) (hi : i∈s) : ⌊|t-occurrenceOrdinate i|⌋₊ ∈ Finset.range N :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hs i hi)))
  rw [← Finset.sum_fiberwise_of_maps_to hn]
  have hL := localization_log_ge_one T hT
  have hb (n : ℕ) (hn : n∈Finset.range N) :
      (∑ i ∈ s with ⌊|t-occurrenceOrdinate i|⌋₊=n,
        |t-occurrenceOrdinate i| *ordinateKernel (t-occurrenceOrdinate i)) ≤
        (8*C*Real.log (2*T+2))/((n:ℝ)+1) := by
    have hnT : (n:ℝ)≤T := (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).trans
      (Nat.floor_le (by linarith))
    have ha : |t-(n:ℝ)-1|≤4*T+2 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hb : |t+(n:ℝ)|≤4*T+2 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hca := (hcount (t-(n:ℝ)-1)).trans (mul_le_mul_of_nonneg_left (localization_local_log T _ hT ha) hC.le)
    have hcb := (hcount (t+n)).trans (mul_le_mul_of_nonneg_left (localization_local_log T _ hT hb) hC.le)
    have he : t-(n:ℝ)-1+1=t-n := by ring
    rw [he] at hca
    have hsub : (s.filter (fun i => ⌊|t-occurrenceOrdinate i|⌋₊=n)) ⊆
        occurrenceInterval (t-(n:ℝ)-1) (t-n) ∪ occurrenceInterval (t+n) (t+n+1) := by
      intro i hi
      exact unit_shell_cover t n i (Finset.mem_filter.mp hi).2
    have hc : ((s.filter (fun i => ⌊|t-occurrenceOrdinate i|⌋₊=n)).card:ℝ) ≤
        4*C*Real.log (2*T+2) := by
      have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hh' : ((s.filter (fun i => ⌊|t-occurrenceOrdinate i|⌋₊=n)).card:ℝ) ≤
        (occurrenceInterval (t-(n:ℝ)-1) (t-n)).card+
        (occurrenceInterval (t+n) (t+n+1)).card := by exact_mod_cast hh
      linarith
    calc
      _ ≤ ∑ _i ∈ s with ⌊|t-occurrenceOrdinate _i|⌋₊=n, 2/((n:ℝ)+1) := by
        apply Finset.sum_le_sum
        intro i hi
        apply localization_unit_shell_weight
        rw [← (Finset.mem_filter.mp hi).2]
        exact Nat.floor_le (abs_nonneg _)
      _ = ((s.filter (fun i => ⌊|t-occurrenceOrdinate i|⌋₊=n)).card:ℝ)*(2/((n:ℝ)+1)) := by simp
      _ ≤ (4*C*Real.log (2*T+2))*(2/((n:ℝ)+1)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hsum : (∑ n ∈ Finset.range N, 1/((n:ℝ)+1)) ≤ 2*Real.log (2*T+2) := by
    have hh := harmonic_le_one_add_log N
    have hNp : 0<(N:ℝ) := by dsimp [N]; positivity
    have hl := Real.log_le_log hNp (show (N:ℝ)≤2*T+2 by linarith)
    have he : (harmonic N:ℝ) = ∑ n ∈ Finset.range N, 1/((n:ℝ)+1) := by
      simp [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add, div_eq_mul_inv]
    rw [he] at hh
    linarith
  calc
    _ ≤ ∑ n ∈ Finset.range N, (8*C*Real.log (2*T+2))/((n:ℝ)+1) := Finset.sum_le_sum hb
    _ = (8*C*Real.log (2*T+2))*(∑ n ∈ Finset.range N, 1/((n:ℝ)+1)) := by rw [Finset.mul_sum]; congr 1; ext n; ring
    _ ≤ (8*C*Real.log (2*T+2))*(2*Real.log (2*T+2)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end
end HigherCorrelations
