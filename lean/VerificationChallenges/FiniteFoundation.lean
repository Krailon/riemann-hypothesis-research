import HigherCorrelations.FiniteDefinitions
import HigherCorrelations.Definitions

/-! Specification only: intentional sorry terms; no solution imports this file. -/
namespace HigherCorrelations

theorem classifyTriple_iff {A : Type*} [DecidableEq A] (v : Fin 3 → A)
    (p : TriplePattern) : classifyTriple v = p ↔ HasPattern p v := by sorry

theorem pattern_unique {A : Type*} [DecidableEq A] (v : Fin 3 → A) :
    ∃! p, HasPattern p v := by sorry

theorem pattern_disjoint {A : Type*} [DecidableEq A] (v : Fin 3 → A)
    {p q : TriplePattern} (hpq : p ≠ q) : ¬ (HasPattern p v ∧ HasPattern q v) := by sorry

theorem sum_regroup_fibers {I A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (D : Finset I) (q : I → A) (f : I → M) :
    (∑ i ∈ D, f i) = ∑ a ∈ D.image q, ∑ i ∈ D.filter (fun i => q i = a), f i := by sorry

theorem sum_regroup_multiplicity {I A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (D : Finset I) (q : I → A) (g : A → M) :
    (∑ i ∈ D, g (q i)) =
      ∑ a ∈ D.image q, (D.filter (fun i => q i = a)).card • g a := by sorry

theorem sum_triple_patterns {I A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (q : I → A) (S : Fin 3 → Finset I) (f : (Fin 3 → I) → M) :
    (∑ t ∈ tripleDomain S, f t) =
      ∑ p : TriplePattern, ∑ t ∈ patternDomain q S p, f t := by sorry

theorem reflectSlots_involutive {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (e : Fin 3 → Bool) : Function.Involutive (reflectSlots r e) := by sorry

theorem reflectSlots_bijective {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (e : Fin 3 → Bool) : Function.Bijective (reflectSlots r e) := by sorry

theorem reflectSlots_labels {I A : Type*} (r : I → I) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (e : Fin 3 → Bool) (t : Fin 3 → I) :
    q ∘ reflectSlots r e t = q ∘ t := by sorry

theorem reflectSlots_domain {I : Type*} (r : I → I)
    (S : Fin 3 → Finset I) (hS : ∀ j i, i ∈ S j → r i ∈ S j)
    (e : Fin 3 → Bool) {t : Fin 3 → I} (ht : t ∈ tripleDomain S) :
    reflectSlots r e t ∈ tripleDomain S := by sorry

theorem reflectSlots_pattern {I A : Type*} [DecidableEq A]
    (r : I → I) (q : I → A) (hq : ∀ i, q (r i) = q i)
    (e : Fin 3 → Bool) (t : Fin 3 → I) :
    classifyTriple (q ∘ reflectSlots r e t) = classifyTriple (q ∘ t) := by sorry

theorem sum_involution {I M : Type*} [AddCommMonoid M] (D : Finset I)
    (r : I → I) (hr : Function.Involutive r) (hD : ∀ i ∈ D, r i ∈ D) (f : I → M) :
    (∑ i ∈ D, f (r i)) = ∑ i ∈ D, f i := by sorry

theorem sum_reflectSlots {I M : Type*} [AddCommMonoid M]
    (r : I → I) (hr : Function.Involutive r) (S : Fin 3 → Finset I)
    (hS : ∀ j i, i ∈ S j → r i ∈ S j) (e : Fin 3 → Bool)
    (f : (Fin 3 → I) → M) :
    (∑ t ∈ tripleDomain S, f (reflectSlots r e t)) = ∑ t ∈ tripleDomain S, f t := by sorry

theorem sum_reflectSlots_pattern {I A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (r : I → I) (hr : Function.Involutive r) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (S : Fin 3 → Finset I)
    (hS : ∀ j i, i ∈ S j → r i ∈ S j) (e : Fin 3 → Bool)
    (p : TriplePattern) (f : (Fin 3 → I) → M) :
    (∑ t ∈ patternDomain q S p, f (reflectSlots r e t)) =
      ∑ t ∈ patternDomain q S p, f t := by sorry

theorem sum_eight_reflections {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (S : Fin 3 → Finset I) (hS : ∀ j i, i ∈ S j → r i ∈ S j)
    (f : (Fin 3 → I) → ℂ) :
    (∑ t ∈ tripleDomain S, f t) =
      (1 / 8 : ℂ) * ∑ e : Fin 3 → Bool, ∑ t ∈ tripleDomain S, f (reflectSlots r e t) := by sorry

theorem sum_eight_reflections_pattern {I A : Type*} [DecidableEq A]
    (r : I → I) (hr : Function.Involutive r) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (S : Fin 3 → Finset I)
    (hS : ∀ j i, i ∈ S j → r i ∈ S j) (p : TriplePattern)
    (f : (Fin 3 → I) → ℂ) :
    (∑ t ∈ patternDomain q S p, f t) =
      (1 / 8 : ℂ) * ∑ e : Fin 3 → Bool, ∑ t ∈ patternDomain q S p, f (reflectSlots r e t) := by sorry

theorem simultaneous_index_pattern {I : Type*} [DecidableEq I]
    (r : I → I) (hr : Function.Involutive r) (t : Fin 3 → I) :
    classifyTriple (reflectSlots r (fun _ => true) t) = classifyTriple t := by sorry

theorem independent_index_counterexample :
    classifyTriple (fun _ : Fin 3 => false) = .allEqual ∧
    classifyTriple (reflectSlots Bool.not (fun j => decide (j = 0))
      (fun _ : Fin 3 => false)) = .only12 := by sorry

theorem sign_product_expansion (e : Fin 3 → Bool) (C S : Fin 3 → ℂ) :
    (∏ j, (C j + reflectionSign (e j) * S j)) =
      ∑ s : Finset (Fin 3), signCharacter s e * (∏ j ∈ s, S j) * (∏ j ∈ sᶜ, C j) := by sorry

theorem weighted_sign_product (K : (Fin 3 → Bool) → ℂ) (C S : Fin 3 → ℂ) :
    (1 / 8 : ℂ) * ∑ e, K e * (∏ j, (C j + reflectionSign (e j) * S j)) =
      ∑ s : Finset (Fin 3), signCoefficient K s * (∏ j ∈ s, S j) * (∏ j ∈ sᶜ, C j) := by sorry

theorem weighted_sign_sub_one (K : (Fin 3 → Bool) → ℂ) (C S : Fin 3 → ℂ) :
    (1 / 8 : ℂ) * ∑ e, K e * ((∏ j, (C j + reflectionSign (e j) * S j)) - 1) =
      (∑ s : Finset (Fin 3), signCoefficient K s * (∏ j ∈ s, S j) *
        (∏ j ∈ sᶜ, C j)) - signCoefficient K ∅ := by sorry

theorem weighted_sign_empty_split (K : (Fin 3 → Bool) → ℂ) (C S : Fin 3 → ℂ) :
    (1 / 8 : ℂ) * ∑ e, K e * ((∏ j, (C j + reflectionSign (e j) * S j)) - 1) =
      signCoefficient K ∅ * ((∏ j, C j) - 1) +
      ∑ s ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
        signCoefficient K s * (∏ j ∈ s, S j) * (∏ j ∈ sᶜ, C j) := by sorry

theorem reflected_zero {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    IsCriticalStripZero (1 - ρ) := by sorry

theorem horizontalReflection_involutive : Function.Involutive horizontalReflection := by sorry

theorem horizontalReflection_im (ρ : ℂ) : (horizontalReflection ρ).im = ρ.im := by sorry

theorem horizontalReflection_displacement (ρ : ℂ) :
    (horizontalReflection ρ).re - (1 / 2 : ℝ) = -(ρ.re - (1 / 2 : ℝ)) := by sorry

theorem horizontalReflection_zero {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    IsCriticalStripZero (horizontalReflection ρ) := by sorry

theorem example_five_patterns :
    classifyTriple ![0, 0, 0] = .allEqual ∧
    classifyTriple ![0, 0, 1] = .only01 ∧
    classifyTriple ![0, 1, 0] = .only02 ∧
    classifyTriple ![0, 1, 1] = .only12 ∧
    classifyTriple ![0, 1, 2] = .allDistinct := by sorry

theorem example_empty_domain :
    (tripleDomain ![∅, {0, 1}, {2, 3}] : Finset (Fin 3 → ℕ)).card = 0 := by sorry

theorem example_singleton_domain :
    (tripleDomain ![{0}, {1}, {2}] : Finset (Fin 3 → ℕ)).card = 1 := by sorry

theorem example_different_cutoffs :
    (tripleDomain ![{0}, {0, 1}, {2, 3, 4}] : Finset (Fin 3 → ℕ)).card = 6 := by sorry

theorem example_repeated_occurrences :
    (∑ i : Fin 3, (![2, 2, 5] : Fin 3 → ℕ) i) = 9 ∧
    (∑ a ∈ (Finset.univ : Finset (Fin 3)).image (![0, 0, 1] : Fin 3 → ℕ),
      if a = 0 then 2 else 5) = 7 ∧
    ((Finset.univ : Finset (Fin 3)).filter (fun i => (![0, 0, 1] : Fin 3 → ℕ) i = 0)).card = 2 := by sorry

theorem example_distinct_complex_same_ordinate :
    let t : Fin 3 → ℂ := ![(1 / 4 : ℂ) + 3 * Complex.I, (3 / 4 : ℂ) + 3 * Complex.I,
      (1 / 4 : ℂ) + 3 * Complex.I]
    classifyTriple (Complex.im ∘ t) = .allEqual ∧ classifyTriple t = .only02 := by sorry

theorem example_fixed_point (y : ℝ) :
    horizontalReflection ((1 / 2 : ℂ) + y * Complex.I) = (1 / 2 : ℂ) + y * Complex.I := by sorry

theorem example_exchanged_pair :
    horizontalReflection ((1 / 4 : ℂ) + 3 * Complex.I) = (3 / 4 : ℂ) + 3 * Complex.I := by sorry

end HigherCorrelations
