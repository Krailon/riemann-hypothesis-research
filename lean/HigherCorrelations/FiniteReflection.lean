import HigherCorrelations.FinitePatterns

/-! UNCONDITIONAL finite reflection identities with explicit occurrence involution.
No enumeration or multiplicity theorem for analytic zeta zeros is assumed here.
-/
namespace HigherCorrelations

theorem reflectSlots_involutive {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (e : Fin 3 → Bool) : Function.Involutive (reflectSlots r e) := by
  intro t
  funext j
  simp only [reflectSlots]
  cases e j
  · rfl
  · exact hr (t j)

theorem reflectSlots_bijective {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (e : Fin 3 → Bool) : Function.Bijective (reflectSlots r e) :=
  (reflectSlots_involutive r hr e).bijective

theorem reflectSlots_labels {I A : Type*} (r : I → I) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (e : Fin 3 → Bool) (t : Fin 3 → I) :
    q ∘ reflectSlots r e t = q ∘ t := by
  funext j
  simp only [Function.comp_apply, reflectSlots]
  cases e j <;> simp [hq]

theorem reflectSlots_domain {I : Type*} (r : I → I)
    (S : Fin 3 → Finset I) (hS : ∀ j i, i ∈ S j → r i ∈ S j)
    (e : Fin 3 → Bool) {t : Fin 3 → I} (ht : t ∈ tripleDomain S) :
    reflectSlots r e t ∈ tripleDomain S := by
  rw [tripleDomain, Fintype.mem_piFinset] at ht ⊢
  intro j
  simp only [reflectSlots]
  cases e j <;> simp [ht j, hS j (t j) (ht j)]

theorem reflectSlots_pattern {I A : Type*} [DecidableEq A]
    (r : I → I) (q : I → A) (hq : ∀ i, q (r i) = q i)
    (e : Fin 3 → Bool) (t : Fin 3 → I) :
    classifyTriple (q ∘ reflectSlots r e t) = classifyTriple (q ∘ t) := by
  rw [reflectSlots_labels r q hq]

theorem sum_involution {I M : Type*} [AddCommMonoid M] (D : Finset I)
    (r : I → I) (hr : Function.Involutive r) (hD : ∀ i ∈ D, r i ∈ D) (f : I → M) :
    (∑ i ∈ D, f (r i)) = ∑ i ∈ D, f i := by
  exact Finset.sum_nbij' r r hD hD (fun i _ => hr i) (fun i _ => hr i) (fun _ _ => rfl)

theorem sum_reflectSlots {I M : Type*} [AddCommMonoid M]
    (r : I → I) (hr : Function.Involutive r) (S : Fin 3 → Finset I)
    (hS : ∀ j i, i ∈ S j → r i ∈ S j) (e : Fin 3 → Bool)
    (f : (Fin 3 → I) → M) :
    (∑ t ∈ tripleDomain S, f (reflectSlots r e t)) = ∑ t ∈ tripleDomain S, f t := by
  exact sum_involution _ _ (reflectSlots_involutive r hr e)
    (fun _ ht => reflectSlots_domain r S hS e ht) f

theorem sum_reflectSlots_pattern {I A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (r : I → I) (hr : Function.Involutive r) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (S : Fin 3 → Finset I)
    (hS : ∀ j i, i ∈ S j → r i ∈ S j) (e : Fin 3 → Bool)
    (p : TriplePattern) (f : (Fin 3 → I) → M) :
    (∑ t ∈ patternDomain q S p, f (reflectSlots r e t)) =
      ∑ t ∈ patternDomain q S p, f t := by
  apply sum_involution _ _ (reflectSlots_involutive r hr e) _ f
  intro t ht
  obtain ⟨hd, hp⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨reflectSlots_domain r S hS e hd,
    (reflectSlots_pattern r q hq e t).trans hp⟩

theorem sum_eight_reflections {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (S : Fin 3 → Finset I) (hS : ∀ j i, i ∈ S j → r i ∈ S j)
    (f : (Fin 3 → I) → ℂ) :
    (∑ t ∈ tripleDomain S, f t) =
      (1 / 8 : ℂ) * ∑ e : Fin 3 → Bool, ∑ t ∈ tripleDomain S, f (reflectSlots r e t) := by
  simp_rw [sum_reflectSlots r hr S hS]
  simp [Fintype.card_pi]

theorem sum_eight_reflections_pattern {I A : Type*} [DecidableEq A]
    (r : I → I) (hr : Function.Involutive r) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (S : Fin 3 → Finset I)
    (hS : ∀ j i, i ∈ S j → r i ∈ S j) (p : TriplePattern)
    (f : (Fin 3 → I) → ℂ) :
    (∑ t ∈ patternDomain q S p, f t) =
      (1 / 8 : ℂ) * ∑ e : Fin 3 → Bool, ∑ t ∈ patternDomain q S p, f (reflectSlots r e t) := by
  simp_rw [sum_reflectSlots_pattern r hr q hq S hS]
  simp [Fintype.card_pi]

theorem simultaneous_index_pattern {I : Type*} [DecidableEq I]
    (r : I → I) (hr : Function.Involutive r) (t : Fin 3 → I) :
    classifyTriple (reflectSlots r (fun _ => true) t) = classifyTriple t := by
  simp only [classifyTriple, reflectSlots, ↓reduceIte,
    hr.injective.eq_iff]

theorem independent_index_counterexample :
    classifyTriple (fun _ : Fin 3 => false) = .allEqual ∧
    classifyTriple (reflectSlots Bool.not (fun j => decide (j = 0))
      (fun _ : Fin 3 => false)) = .only12 := by decide

end HigherCorrelations
