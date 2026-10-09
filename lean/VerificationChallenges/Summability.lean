import HigherCorrelations.SummabilityDefinitions

/-! Definition-only specifications. Intentional sorry terms; solutions never import this file. -/
namespace HigherCorrelations
open Filter MeasureTheory
open scoped Topology

theorem dyadic_ratio_bounds (d p : ℕ) (hp : d < p) :
    0 ≤ dyadicRatio d p ∧ dyadicRatio d p < 1 := by sorry

theorem shell_sum_eq {I : Type*} (S : OccurrenceShells I) (f : I → ℝ) (n : ℕ) :
    (∑' i : {i // S.shell i = n}, f i) = ∑ i ∈ S.members n, f i := by sorry

theorem summable_of_shell_bounds {I : Type*} (S : OccurrenceShells I)
    (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) (B : ℕ → ℝ) (hB : Summable B)
    (hbound : ∀ n, (∑ i ∈ S.members n, f i) ≤ B n) : Summable f := by sorry

theorem dyadic_shell_sum_bound {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (_hC : 0 ≤ C) (d p : ℕ)
    (hcount : ∀ n, ((S.members n).card : ℝ) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (hdecay : ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i) (n : ℕ) :
    (∑ i ∈ S.members n, ‖f i‖) ≤ A * C * dyadicRatio d p ^ n := by sorry

theorem dyadic_summable_norm {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (d p : ℕ) (hp : d < p)
    (hcount : ∀ n, ((S.members n).card : ℝ) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (hdecay : ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i) :
    Summable (fun i => ‖f i‖) := by sorry

theorem dyadic_summable {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (d p : ℕ) (hp : d < p)
    (hcount : ∀ n, ((S.members n).card : ℝ) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (hdecay : ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i) : Summable f := by sorry

theorem radius_decay_to_shell {I : Type*} (S : OccurrenceShells I)
    (f : I → ℂ) (r : I → ℝ) (A : ℝ) (hA : 0 ≤ A) (p : ℕ)
    (hr : ∀ i, (2 : ℝ) ^ S.shell i ≤ 1 + r i)
    (hf : ∀ i, ‖f i‖ ≤ A / (1 + r i) ^ p) :
    ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i := by sorry

theorem shell_tsum_eq {I : Type*} (S : OccurrenceShells I) (f : I → ℝ)
    (hf : Summable f) :
    (∑' i, f i) = ∑' n, ∑ i ∈ S.members n, f i := by sorry

theorem geometric_tail_eq (a : ℕ → ℝ) (N : ℕ) :
    (∑' n, if N ≤ n then a n else 0) = ∑' n, a (n + N) := by sorry

theorem dyadic_tail_bound {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (d p : ℕ) (hp : d < p)
    (hcount : ∀ n, ((S.members n).card : ℝ) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (hdecay : ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i) (N : ℕ) :
    (∑' i : {i // N ≤ S.shell i}, ‖f i‖) ≤
      A * C * dyadicRatio d p ^ N / (1 - dyadicRatio d p) := by sorry

theorem project_dyadic_ratios :
    dyadicRatio 4 20 = (1 / 65536 : ℝ) ∧
    dyadicRatio 4 22 = (1 / 262144 : ℝ) := by sorry

theorem occurrence_cutoff_limit {I K E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (l : Filter K) (S : K → Finset I) (hS : ∀ i, ∀ᶠ k in l, i ∈ S k)
    (f : I → E) (hf : Summable (fun i => ‖f i‖)) :
    Tendsto (fun k => ∑ i ∈ S k, f i) l (𝓝 (∑' i, f i)) := by sorry

theorem triple_cutoff_limit {I : Type*} (f : (Fin 3 → I) → ℂ)
    (hf : Summable (fun t => ‖f t‖)) :
    Tendsto (fun S : Fin 3 → Finset I => ∑ t ∈ tripleDomain S, f t)
      atTop (𝓝 (∑' t, f t)) := by sorry

theorem independent_sequence_cutoff_limit {I : Type*}
    (S : Fin 3 → ℕ → Finset I) (hS : ∀ j i, ∀ᶠ n in atTop, i ∈ S j n)
    (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    Tendsto (fun N : Fin 3 → ℕ => ∑ t ∈ tripleDomain (fun j => S j (N j)), f t)
      atTop (𝓝 (∑' t, f t)) := by sorry

theorem tsum_regroup_occurrences {I A : Type*} (q : I → A) (f : I → ℂ)
    (hf : Summable (fun i => ‖f i‖)) :
    (∑' i, f i) = ∑' a, ∑' i : {i // q i = a}, f i := by sorry

theorem tsum_regroup_finite_fibers {I A : Type*} (q : I → A)
    (D : A → Finset I) (hD : ∀ i a, i ∈ D a ↔ q i = a) (g : A → ℂ)
    (hf : Summable (fun i => ‖g (q i)‖)) :
    (∑' i, g (q i)) = ∑' a, (D a).card • g a := by sorry

theorem tsum_triple_patterns {I A : Type*} [DecidableEq A]
    (q : I → A) (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    (∑' t, f t) = ∑ p : TriplePattern,
      ∑' t : {t // classifyTriple (q ∘ t) = p}, f t := by sorry

theorem summable_reflectSlots {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (e : Fin 3 → Bool) (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    Summable (fun t => ‖f (reflectSlots r e t)‖) := by sorry

theorem tsum_reflectSlots {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (e : Fin 3 → Bool) (f : (Fin 3 → I) → ℂ) (_hf : Summable (fun t => ‖f t‖)) :
    (∑' t, f (reflectSlots r e t)) = ∑' t, f t := by sorry

theorem tsum_eight_reflections {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    (∑' t, f t) = (1 / 8 : ℂ) *
      ∑ e : Fin 3 → Bool, ∑' t, f (reflectSlots r e t) := by sorry

theorem tsum_reflectSlots_pattern {I A : Type*} [DecidableEq A]
    (r : I → I) (hr : Function.Involutive r) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (e : Fin 3 → Bool) (p : TriplePattern)
    (f : (Fin 3 → I) → ℂ) (_hf : Summable (fun t => ‖f t‖)) :
    (∑' t : {t // classifyTriple (q ∘ t) = p}, f (reflectSlots r e t)) =
      ∑' t : {t // classifyTriple (q ∘ t) = p}, f t := by sorry

theorem tsum_eight_reflections_pattern {I A : Type*} [DecidableEq A]
    (r : I → I) (hr : Function.Involutive r) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (p : TriplePattern)
    (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    (∑' t : {t // classifyTriple (q ∘ t) = p}, f t) = (1 / 8 : ℂ) *
      ∑ e : Fin 3 → Bool, ∑' t : {t // classifyTriple (q ∘ t) = p},
        f (reflectSlots r e t) := by sorry

theorem dominated_occurrence_limit {I K : Type*} (l : Filter K)
    (f : K → I → ℂ) (g : I → ℂ) (B : I → ℝ) (hB : Summable B)
    (hlim : ∀ i, Tendsto (fun k => f k i) l (𝓝 (g i)))
    (hbound : ∀ᶠ k in l, ∀ i, ‖f k i‖ ≤ B i) :
    Tendsto (fun k => ∑' i, f k i) l (𝓝 (∑' i, g i)) := by sorry

theorem evaluated_integrals_summable {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : I → X → ℂ) (_hG : ∀ i, Integrable (G i) μ)
    (B : I → ℝ) (hB : Summable B) (hbound : ∀ i, ‖∫ x, G i x ∂μ‖ ≤ B i) :
    Summable (fun i => ‖∫ x, G i x ∂μ‖) := by sorry

theorem evaluated_integrals_cutoff_limit {I K X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : I → X → ℂ) (hG : ∀ i, Integrable (G i) μ)
    (B : I → ℝ) (hB : Summable B) (hbound : ∀ i, ‖∫ x, G i x ∂μ‖ ≤ B i)
    (l : Filter K) (S : K → Finset I) (hS : ∀ i, ∀ᶠ k in l, i ∈ S k) :
    Tendsto (fun k => ∑ i ∈ S k, ∫ x, G i x ∂μ) l
      (𝓝 (∑' i, ∫ x, G i x ∂μ)) := by sorry

theorem integral_occurrence_sum {I X : Type*} [Countable I] [MeasurableSpace X]
    (μ : Measure X) (G : I → X → ℂ) (hG : ∀ i, Integrable (G i) μ)
    (hL1 : Summable (fun i => ∫ x, ‖G i x‖ ∂μ)) :
    (∑' i, ∫ x, G i x ∂μ) = ∫ x, ∑' i, G i x ∂μ := by sorry

theorem integral_occurrence_cutoff_limit {I K X : Type*}
    [Countable I] [MeasurableSpace X] (μ : Measure X) (G : I → X → ℂ)
    (hG : ∀ i, Integrable (G i) μ)
    (hL1 : Summable (fun i => ∫ x, ‖G i x‖ ∂μ))
    (l : Filter K) (S : K → Finset I) (hS : ∀ i, ∀ᶠ k in l, i ∈ S k) :
    Tendsto (fun k => ∫ x, ∑ i ∈ S k, G i x ∂μ) l
      (𝓝 (∫ x, ∑' i, G i x ∂μ)) := by sorry

theorem dominated_integral_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : ℕ → X → ℂ) (g : X → ℂ) (B : X → ℝ)
    (hG : ∀ n, AEStronglyMeasurable (G n) μ) (hB : Integrable B μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖G n x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by sorry

theorem continuous_cosh_excess {I : Type*} (D : Finset I) (δ : I → ℝ) (b : ℝ) :
    Continuous (fun z : ℝ × ℝ => sameOrdinateCoshSum D δ b z.1 z.2) := by sorry

theorem continuous_frequency_form :
    Continuous (fun z : ℝ × ℝ => horizontalFrequencyForm z.1 z.2) := by sorry

theorem integrable_weighted_cosh {I : Type*} (D : Finset I) (δ : I → ℝ) (b : ℝ)
    (φ : ℝ × ℝ → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => φ z * sameOrdinateCoshSum D δ b z.1 z.2) := by sorry

theorem integrable_weighted_frequency (φ : ℝ × ℝ → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => φ z * horizontalFrequencyForm z.1 z.2) := by sorry

theorem integrated_frequency_nonneg (φ : ℝ × ℝ → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    0 ≤ integratedFrequencyForm φ := by sorry

theorem integrated_cosh_nonneg {I : Type*} (D : Finset I) (δ : I → ℝ) (b : ℝ)
    (φ : ℝ × ℝ → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    0 ≤ integratedCoshExcess D δ b φ := by sorry

theorem integrated_horizontal_square_lower {I : Type*}
    (D : Finset I) (δ : I → ℝ) (b : ℝ) (φ : ℝ × ℝ → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hn : ∀ z, 0 ≤ φ z) :
    b ^ 2 * (D.card : ℝ) ^ 2 * horizontalSquareMass D δ * integratedFrequencyForm φ ≤
      integratedCoshExcess D δ b φ := by sorry

theorem integrated_fibers_lower {I G : Type*} [Countable G]
    (D : G → Finset I) (δ : I → ℝ) (W : G → ℝ) (hW : ∀ g, 0 ≤ W g)
    (b : ℝ) (φ : ℝ × ℝ → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hn : ∀ z, 0 ≤ φ z)
    (hs : Summable (fun g => W g * integratedCoshExcess (D g) δ b φ)) :
    Summable (fun g => W g * (b ^ 2 * ((D g).card : ℝ) ^ 2 *
      horizontalSquareMass (D g) δ * integratedFrequencyForm φ)) ∧
    (∑' g, W g * (b ^ 2 * ((D g).card : ℝ) ^ 2 *
      horizontalSquareMass (D g) δ * integratedFrequencyForm φ)) ≤
      ∑' g, W g * integratedCoshExcess (D g) δ b φ := by sorry

theorem geometric_tail_example (N : ℕ) :
    (∑' n : ℕ, if N ≤ n then (1 / 2 : ℝ) ^ n else 0) =
      2 * (1 / 2 : ℝ) ^ N := by sorry

theorem repeated_labels_tsum_example (z : ℂ) :
    (∑' _i : Fin 2, z) = (2 : ℂ) * z := by sorry

theorem empty_occurrence_tsum_example (f : Empty → ℂ) : (∑' i, f i) = 0 := by sorry

theorem reflection_fixed_point_tsum_example (f : (Fin 3 → ℕ) → ℂ)
    (hf : Summable (fun t => ‖f t‖)) (e : Fin 3 → Bool) :
    (∑' t, f (reflectSlots id e t)) = ∑' t, f t := by sorry

theorem independent_cutoff_example (f : (Fin 3 → ℕ) → ℂ)
    (hf : Summable (fun t => ‖f t‖)) :
    Tendsto (fun N : Fin 3 → ℕ =>
      ∑ t ∈ tripleDomain (fun j => Finset.range (N j + j.val)), f t)
      atTop (𝓝 (∑' t, f t)) := by sorry

theorem integrated_empty_example {I : Type*} (δ : I → ℝ) (b : ℝ)
    (φ : ℝ × ℝ → ℝ) : integratedCoshExcess ∅ δ b φ = 0 := by sorry

theorem integrated_zero_scale_example {I : Type*} (D : Finset I) (δ : I → ℝ)
    (φ : ℝ × ℝ → ℝ) : integratedCoshExcess D δ 0 φ = 0 := by sorry

theorem integrated_zero_weight_example {I : Type*} (D : Finset I) (δ : I → ℝ)
    (b : ℝ) : integratedCoshExcess D δ b (fun _ => 0) = 0 ∧
      integratedFrequencyForm (fun _ => 0) = 0 := by sorry

theorem moving_singleton_summable (n : ℕ) : Summable (movingSingleton n) := by sorry

theorem moving_singleton_sum (n : ℕ) : (∑' i, movingSingleton n i) = 1 := by sorry

theorem moving_singleton_pointwise (i : ℕ) :
    Tendsto (fun n => movingSingleton n i) atTop (𝓝 0) := by sorry

theorem moving_singleton_no_majorant (B : ℕ → ℝ) (hB : Summable B)
    (hbound : ∀ n i, ‖movingSingleton n i‖ ≤ B i) : False := by sorry

theorem moving_singleton_limit_mismatch :
    Tendsto (fun n => ∑' i, movingSingleton n i) atTop (𝓝 1) ∧
    (∑' _i : ℕ, (0 : ℝ)) ≠ 1 := by sorry

theorem singleton_shell_summable_example :
    Summable (fun n : ℕ => ‖(1 / 2 : ℂ) ^ n‖) := by sorry

theorem dyadic_endpoint_example (d : ℕ) :
    dyadicRatio d d = 1 ∧ ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by sorry

end HigherCorrelations
