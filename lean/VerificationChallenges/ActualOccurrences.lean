import HigherCorrelations.ActualCorrelationDefinitions
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Definition-only specifications. Intentional unfinished terms; solutions never import this file. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

theorem stripZero_ne_one (ρ : StripZero) : ρ.val ≠ 1  := by sorry

theorem stripZero_analytic (ρ : StripZero) : AnalyticAt ℂ riemannZeta ρ.val  := by sorry

theorem stripZero_order_finite (ρ : StripZero) : analyticOrderAt riemannZeta ρ.val ≠ ⊤  := by sorry

theorem zeroMultiplicity_pos (ρ : StripZero) : 0 < zeroMultiplicity ρ  := by sorry

theorem zeroMultiplicity_conjugate (ρ : StripZero) :
    zeroMultiplicity (stripZeroConjugate ρ) = zeroMultiplicity ρ  := by sorry

theorem stripZero_height_finite (U : ℝ) :
    Set.Finite {ρ : StripZero | |ρ.val.im| ≤ U}  := by sorry

theorem occurrence_height_finite (U : ℝ) :
    Set.Finite {i : ZeroOccurrence | |occurrenceOrdinate i| ≤ U}  := by sorry

theorem mem_occurrenceCutoff (i : ZeroOccurrence) (U : ℝ) :
    i ∈ occurrenceCutoff U ↔ |occurrenceOrdinate i| ≤ U  := by sorry

theorem occurrenceCutoff_negative (U : ℝ) (hU : U < 0) : occurrenceCutoff U = ∅  := by sorry

theorem occurrenceCutoff_exhausts (i : ZeroOccurrence) :
    ∀ᶠ n : ℕ in atTop, i ∈ occurrenceCutoff n  := by sorry

theorem occurrence_ordinate_finite (γ : ℝ) :
    Set.Finite {i : ZeroOccurrence | occurrenceOrdinate i = γ}  := by sorry

theorem zero_occurrences_countable : Countable ZeroOccurrence  := by sorry

theorem zeroMultiplicity_one_sub (ρ : StripZero) :
    zeroMultiplicity (stripZeroOneSub ρ) = zeroMultiplicity ρ  := by sorry

theorem zeroMultiplicity_horizontalReflection (ρ : StripZero) :
    zeroMultiplicity (stripZeroHorizontalReflection ρ) = zeroMultiplicity ρ  := by sorry

theorem occurrenceReflection_value (i : ZeroOccurrence) :
    occurrenceValue (occurrenceReflection i) = horizontalReflection (occurrenceValue i)  := by sorry

theorem occurrenceReflection_involutive : Function.Involutive occurrenceReflection  := by sorry

theorem occurrenceReflection_ordinate (i : ZeroOccurrence) :
    occurrenceOrdinate (occurrenceReflection i) = occurrenceOrdinate i  := by sorry

theorem occurrenceReflection_displacement (i : ZeroOccurrence) :
    occurrenceDisplacement (occurrenceReflection i) = -occurrenceDisplacement i  := by sorry

theorem occurrence_count_polynomial :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 0 ≤ U →
      ((occurrenceCutoff U).card : ℝ) ≤ C * (1 + U) ^ 2  := by sorry

theorem anchor_finite (T : ℝ) : Finite (AnchorOccurrence T)  := by sorry

theorem dyadicIndex_bounds (r : ℝ) (hr : 0 ≤ r) :
    (2 : ℝ) ^ dyadicIndex r ≤ 1 + r ∧ 1 + r < (2 : ℝ) ^ (dyadicIndex r + 1)  := by sorry

theorem anchoredRadius_nonneg (T a : ℝ) (t : AnchoredTriple T) : 0 ≤ anchoredRadius T a t  := by sorry

theorem actual_shell_cardinality (T a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (Nat.card {t : AnchoredTriple T // dyadicIndex (anchoredRadius T a t) = n} : ℝ) ≤
      C * ((2 : ℝ) ^ 4) ^ n  := by sorry

theorem planeCoords_apply (ξ : FourierPlane) : planeCoords ξ = WithLp.ofLp ξ  := by sorry

theorem complexFourier_integrable (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (z : ℂ × ℂ) :
    Integrable (fun ξ : ℝ × ℝ => φ ξ * Complex.exp
      (2 * Real.pi * Complex.I * (z.1 * ξ.1 + z.2 * ξ.2)))  := by sorry

theorem complexFourier_eq_inverse (φ : ℝ × ℝ → ℂ) (x y : ℝ × ℝ) :
    complexFourier φ (complexPair x y) = 𝓕⁻ (twistedAmplitude φ y) (WithLp.toLp 2 x)  := by sorry

theorem complexFourier_real_eq_inverse (φ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    complexFourier φ ((x.1 : ℂ), (x.2 : ℂ)) =
      𝓕⁻ (fun ξ : FourierPlane => φ (WithLp.ofLp ξ)) (WithLp.toLp 2 x)  := by sorry

theorem complexFourier_strip_decay (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (B : ℝ) (_hB : 0 ≤ B) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ × ℝ, |y.1| ≤ B → |y.2| ≤ B →
      ‖complexFourier φ (complexPair x y)‖ ≤ C / (1 + max |x.1| |x.2|) ^ n  := by sorry

theorem occurrence_displacement_lt (i : ZeroOccurrence) : |occurrenceDisplacement i| < 1 / 2  := by sorry

theorem actualShifts_bound (a : ℝ) (ha : 0 ≤ a) (t : Fin 3 → ZeroOccurrence) :
    |(actualShifts a t).1| ≤ a ∧ |(actualShifts a t).2| ≤ a  := by sorry

theorem meanSpacing_pos (T : ℝ) (hT : 2 * Real.pi < T) : 0 < meanSpacing T  := by sorry

theorem anchored_actual_summable_norm (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    Summable (fun t : AnchoredTriple T => ‖actualCorrelationTerm a w φ b (anchoredToTriple t)‖)  := by sorry

theorem actual_anchored_tail (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (b : Bool) (p : ℕ) (hp : 4 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      (∑' t : {t : AnchoredTriple T // N ≤ dyadicIndex (anchoredRadius T a t)},
        ‖actualCorrelationTerm a w φ b (anchoredToTriple t.val)‖) ≤
      K * dyadicRatio 4 p ^ N / (1 - dyadicRatio 4 p)  := by sorry

theorem actual_summable_norm (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    Summable (fun t : Fin 3 → ZeroOccurrence => ‖actualCorrelationTerm a w φ b t‖)  := by sorry

theorem actual_signed_difference_summable (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Summable (fun t : Fin 3 → ZeroOccurrence =>
      ‖actualCorrelationTerm a w φ true t - actualCorrelationTerm a w φ false t‖)  := by sorry

theorem actual_independent_cutoff_limit (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    Tendsto (fun N : Fin 3 → ℕ => ∑ t ∈ tripleDomain (fun j => occurrenceCutoff (N j)),
      actualCorrelationTerm a w φ b t) atTop (𝓝 (∑' t, actualCorrelationTerm a w φ b t))  := by sorry

theorem actual_signed_cutoff_limit (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Tendsto (fun N : Fin 3 → ℕ => ∑ t ∈ tripleDomain (fun j => occurrenceCutoff (N j)),
      (actualCorrelationTerm a w φ true t - actualCorrelationTerm a w φ false t)) atTop
      (𝓝 (∑' t, (actualCorrelationTerm a w φ true t - actualCorrelationTerm a w φ false t)))  := by sorry

theorem project_actual_summable_norm (T : ℝ) (hT : 2 * Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    Summable (fun t : Fin 3 → ZeroOccurrence => ‖actualCorrelationTerm (meanSpacing T) w φ b t‖)  := by sorry

theorem zero_occurrence_fiber_card (ρ : StripZero) :
    Nat.card {i : ZeroOccurrence // i.1 = ρ} = zeroMultiplicity ρ  := by sorry

theorem actual_ordinate_regroup (f : ZeroOccurrence → ℂ)
    (hf : Summable (fun i => ‖f i‖)) :
    (∑' i, f i) = ∑' γ : ℝ, ∑' i : {i // occurrenceOrdinate i = γ}, f i  := by sorry

theorem actual_triple_patterns (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    (∑' t, actualCorrelationTerm a w φ b t) = ∑ p : TriplePattern,
      ∑' t : {t // classifyTriple (occurrenceOrdinate ∘ t) = p}, actualCorrelationTerm a w φ b t  := by sorry

theorem actual_eight_reflections (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : Bool) :
    (∑' t, actualCorrelationTerm a w φ b t) = (1 / 8 : ℂ) *
      ∑ e : Fin 3 → Bool, ∑' t, actualCorrelationTerm a w φ b (reflectSlots occurrenceReflection e t)  := by sorry

theorem actual_signed_eight_reflections (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2 * T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∑' t, (actualCorrelationTerm a w φ true t - actualCorrelationTerm a w φ false t)) =
      (1 / 8 : ℂ) * ∑ e : Fin 3 → Bool, ∑' t,
        (actualCorrelationTerm a w φ true (reflectSlots occurrenceReflection e t) -
         actualCorrelationTerm a w φ false (reflectSlots occurrenceReflection e t))  := by sorry

theorem actual_reflection_preserves_patterns (e : Fin 3 → Bool) (t : Fin 3 → ZeroOccurrence) :
    classifyTriple (occurrenceOrdinate ∘ reflectSlots occurrenceReflection e t) =
      classifyTriple (occurrenceOrdinate ∘ t)  := by sorry

theorem actual_cutoff_endpoint (i : ZeroOccurrence) : i ∈ occurrenceCutoff |occurrenceOrdinate i|  := by sorry

theorem actual_reflection_cutoff (i : ZeroOccurrence) (U : ℝ) :
    occurrenceReflection i ∈ occurrenceCutoff U ↔ i ∈ occurrenceCutoff U  := by sorry

theorem actual_zero_test (a : ℝ) (w : ℝ → ℂ) (b : Bool) (t : Fin 3 → ZeroOccurrence) :
    actualCorrelationTerm a w (fun _ => 0) b t = 0  := by sorry

theorem complexPair_zero_band (x : ℝ × ℝ) : complexPair x (0, 0) = ((x.1 : ℂ), (x.2 : ℂ))  := by sorry

end
end HigherCorrelations
