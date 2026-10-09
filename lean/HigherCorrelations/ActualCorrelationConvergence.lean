import HigherCorrelations.ZeroOccurrenceShells
import HigherCorrelations.ZeroOccurrenceReflection
import HigherCorrelations.ComplexFourierDecay
import HigherCorrelations.OccurrenceLimits

/-! Absolute convergence for actual real and complex test arguments. UNCONDITIONAL.
Fix T, scale, anchor weight, and Fourier test before removing independent cutoffs.
-/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology ContDiff

theorem occurrence_displacement_lt (i : ZeroOccurrence) : |occurrenceDisplacement i| < 1 / 2 := by
  have h := i.1.property.2
  change |i.1.val.re - 1 / 2| < 1 / 2
  exact abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

theorem actualShifts_bound (a : ℝ) (ha : 0 ≤ a) (t : Fin 3 → ZeroOccurrence) :
    |(actualShifts a t).1| ≤ a ∧ |(actualShifts a t).2| ≤ a := by
  have hh (i j : ZeroOccurrence) : |a * (occurrenceDisplacement i + occurrenceDisplacement j)| ≤ a := by
    rw [abs_mul, abs_of_nonneg ha]
    have hb := abs_add_le (occurrenceDisplacement i) (occurrenceDisplacement j)
    have h₁ := occurrence_displacement_lt i
    have h₂ := occurrence_displacement_lt j
    nlinarith
  exact ⟨hh _ _, hh _ _⟩

theorem meanSpacing_pos (T : ℝ) (hT : 2 * Real.pi < T) : 0 < meanSpacing T := by
  apply div_pos (Real.log_pos _) (by positivity)
  exact (one_lt_div (by positivity)).mpr hT

private theorem anchored_term_decay (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (b : Bool) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : AnchoredTriple T,
      ‖actualCorrelationTerm a w φ b (anchoredToTriple t)‖ ≤ A / (1 + anchoredRadius T a t) ^ n := by
  classical
  obtain ⟨C, hC, hb⟩ := complexFourier_strip_decay φ hφ hc a ha.le n
  let W : ℝ := ∑ i : AnchorOccurrence T, ‖w (occurrenceOrdinate i.val)‖
  have hW : 0 ≤ W := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  refine ⟨W * C, mul_nonneg hW hC.le, ?_⟩
  intro t
  have hw : ‖w (occurrenceOrdinate t.1.val)‖ ≤ W :=
    Finset.single_le_sum (fun i _ => norm_nonneg (w (occurrenceOrdinate i.val))) (Finset.mem_univ t.1)
  let x := actualGaps a (anchoredToTriple t)
  let y := if b then actualShifts a (anchoredToTriple t) else (0, 0)
  have hy : |y.1| ≤ a ∧ |y.2| ≤ a := by
    dsimp [y]
    cases b
    · simpa using And.intro ha.le ha.le
    · exact actualShifts_bound a ha.le _
  have hd := hb x y hy.1 hy.2
  have hr : max |x.1| |x.2| = anchoredRadius T a t := rfl
  change ‖w (occurrenceOrdinate t.1.val) * complexFourier φ (complexPair x y)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ W * (C / (1 + anchoredRadius T a t) ^ n) := by
      apply mul_le_mul hw _ (norm_nonneg _) hW
      simpa only [hr] using hd
    _ = _ := by ring

theorem anchored_actual_summable_norm (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    Summable (fun t : AnchoredTriple T => ‖actualCorrelationTerm a w φ b (anchoredToTriple t)‖) := by
  obtain ⟨C, hC, hcount⟩ := actual_shell_count T a ha
  obtain ⟨A, hA, hdecay⟩ := anchored_term_decay T a ha w φ hφ hc b 20
  exact dyadic_summable_norm (actualOccurrenceShells T a ha) _ A C hA hC 4 20 (by norm_num)
    hcount (radius_decay_to_shell _ _ _ A hA 20 (actual_shell_radius_lower T a ha) hdecay)

theorem actual_anchored_tail (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (b : Bool) (p : ℕ) (hp : 4 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      (∑' t : {t : AnchoredTriple T // N ≤ dyadicIndex (anchoredRadius T a t)},
        ‖actualCorrelationTerm a w φ b (anchoredToTriple t.val)‖) ≤
      K * dyadicRatio 4 p ^ N / (1 - dyadicRatio 4 p) := by
  obtain ⟨C, hC, hcount⟩ := actual_shell_count T a ha
  obtain ⟨A, hA, hdecay⟩ := anchored_term_decay T a ha w φ hφ hc b p
  exact ⟨A * C, mul_nonneg hA hC, fun N =>
    dyadic_tail_bound (actualOccurrenceShells T a ha) _ A C hA hC 4 p hp hcount
      (radius_decay_to_shell _ _ _ A hA p (actual_shell_radius_lower T a ha) hdecay) N⟩

private def anchoredTripleEquiv (T : ℝ) : AnchoredTriple T ≃
    {t : Fin 3 → ZeroOccurrence // T ≤ occurrenceOrdinate (t 0) ∧ occurrenceOrdinate (t 0) ≤ 2 * T} where
  toFun t := ⟨anchoredToTriple t, t.1.property⟩
  invFun t := (⟨t.val 0, t.property⟩, t.val 1, t.val 2)
  left_inv _ := rfl
  right_inv t := by
    apply Subtype.ext
    funext j
    fin_cases j <;> rfl

theorem actual_summable_norm (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    Summable (fun t : Fin 3 → ZeroOccurrence => ‖actualCorrelationTerm a w φ b t‖) := by
  classical
  have hs := anchored_actual_summable_norm T a ha w φ hφ hc b
  have ht : Summable (fun t : {t : Fin 3 → ZeroOccurrence //
      T ≤ occurrenceOrdinate (t 0) ∧ occurrenceOrdinate (t 0) ≤ 2 * T} =>
      ‖actualCorrelationTerm a w φ b t.val‖) := by
    apply (Equiv.summable_iff (anchoredTripleEquiv T)
      (f := fun t => ‖actualCorrelationTerm a w φ b t.val‖)).mp
    dsimp only [Function.comp_def, anchoredTripleEquiv, Equiv.coe_fn_mk]
    exact hs
  have hi : Summable ({t : Fin 3 → ZeroOccurrence | T ≤ occurrenceOrdinate (t 0) ∧
      occurrenceOrdinate (t 0) ≤ 2 * T}.indicator (fun t => ‖actualCorrelationTerm a w φ b t‖)) :=
    summable_subtype_iff_indicator.mp ht
  apply hi.congr
  intro t
  by_cases hm : T ≤ occurrenceOrdinate (t 0) ∧ occurrenceOrdinate (t 0) ≤ 2 * T
  · simp [hm]
  · simp [hm, actualCorrelationTerm, hw _ hm]

theorem actual_signed_difference_summable (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Summable (fun t : Fin 3 → ZeroOccurrence =>
      ‖actualCorrelationTerm a w φ true t - actualCorrelationTerm a w φ false t‖) := by
  exact ((actual_summable_norm T a ha w hw φ hφ hc true).of_norm.sub
    (actual_summable_norm T a ha w hw φ hφ hc false).of_norm).norm

theorem actual_independent_cutoff_limit (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    Tendsto (fun N : Fin 3 → ℕ => ∑ t ∈ tripleDomain (fun j => occurrenceCutoff (N j)),
      actualCorrelationTerm a w φ b t) atTop (𝓝 (∑' t, actualCorrelationTerm a w φ b t)) :=
  independent_sequence_cutoff_limit (fun _ n => occurrenceCutoff n)
    (fun _ i => occurrenceCutoff_exhausts i) _ (actual_summable_norm T a ha w hw φ hφ hc b)

theorem actual_signed_cutoff_limit (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Tendsto (fun N : Fin 3 → ℕ => ∑ t ∈ tripleDomain (fun j => occurrenceCutoff (N j)),
      (actualCorrelationTerm a w φ true t - actualCorrelationTerm a w φ false t)) atTop
      (𝓝 (∑' t, (actualCorrelationTerm a w φ true t - actualCorrelationTerm a w φ false t))) :=
  independent_sequence_cutoff_limit (fun _ n => occurrenceCutoff n)
    (fun _ i => occurrenceCutoff_exhausts i) _ (actual_signed_difference_summable T a ha w hw φ hφ hc)

theorem project_actual_summable_norm (T : ℝ) (hT : 2 * Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    Summable (fun t : Fin 3 → ZeroOccurrence => ‖actualCorrelationTerm (meanSpacing T) w φ b t‖) :=
  actual_summable_norm T (meanSpacing T) (meanSpacing_pos T hT) w hw φ hφ hc b

end
end HigherCorrelations
