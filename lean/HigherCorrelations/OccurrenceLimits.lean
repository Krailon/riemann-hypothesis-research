import HigherCorrelations.SummabilityDefinitions
import HigherCorrelations.FiniteReflection

/-! UNCONDITIONAL absolutely convergent occurrence sums and limit implications.
No enumeration or counting theorem for actual zeta zeros is asserted.
-/
namespace HigherCorrelations
open Filter
open scoped Topology

theorem occurrence_cutoff_limit {I K E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (l : Filter K) (S : K → Finset I) (hS : ∀ i, ∀ᶠ k in l, i ∈ S k)
    (f : I → E) (hf : Summable (fun i => ‖f i‖)) :
    Tendsto (fun k => ∑ i ∈ S k, f i) l (𝓝 (∑' i, f i)) := by
  have hcofinal : Tendsto S l atTop := by
    apply tendsto_atTop.mpr
    intro D
    exact D.eventually_all.mpr (fun i _ => hS i)
  exact (show Tendsto (fun D : Finset I => ∑ i ∈ D, f i) atTop
    (𝓝 (∑' i, f i)) from hf.of_norm.hasSum).comp hcofinal

theorem triple_cutoff_limit {I : Type*} (f : (Fin 3 → I) → ℂ)
    (hf : Summable (fun t => ‖f t‖)) :
    Tendsto (fun S : Fin 3 → Finset I => ∑ t ∈ tripleDomain S, f t)
      atTop (𝓝 (∑' t, f t)) := by
  classical
  apply occurrence_cutoff_limit atTop tripleDomain _ f hf
  intro t
  apply eventually_atTop.mpr
  refine ⟨fun j => {t j}, ?_⟩
  intro S hS
  rw [tripleDomain, Fintype.mem_piFinset]
  intro j
  exact hS j (Finset.mem_singleton_self _)

theorem independent_sequence_cutoff_limit {I : Type*}
    (S : Fin 3 → ℕ → Finset I) (hS : ∀ j i, ∀ᶠ n in atTop, i ∈ S j n)
    (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    Tendsto (fun N : Fin 3 → ℕ => ∑ t ∈ tripleDomain (fun j => S j (N j)), f t)
      atTop (𝓝 (∑' t, f t)) := by
  apply occurrence_cutoff_limit atTop _ _ f hf
  intro t
  choose N hN using fun j => eventually_atTop.mp (hS j (t j))
  apply eventually_atTop.mpr
  refine ⟨N, ?_⟩
  intro M hM
  rw [tripleDomain, Fintype.mem_piFinset]
  exact fun j => hN j (M j) (hM j)

theorem tsum_regroup_occurrences {I A : Type*} (q : I → A) (f : I → ℂ)
    (hf : Summable (fun i => ‖f i‖)) :
    (∑' i, f i) = ∑' a, ∑' i : {i // q i = a}, f i := by
  exact (hf.of_norm.hasSum.tsum_fiberwise q).tsum_eq.symm

theorem tsum_regroup_finite_fibers {I A : Type*} (q : I → A)
    (D : A → Finset I) (hD : ∀ i a, i ∈ D a ↔ q i = a) (g : A → ℂ)
    (hf : Summable (fun i => ‖g (q i)‖)) :
    (∑' i, g (q i)) = ∑' a, (D a).card • g a := by
  rw [tsum_regroup_occurrences q _ hf]
  apply tsum_congr
  intro a
  have hset : {i | q i = a} = (D a : Set I) := by
    ext i; exact (hD i a).symm
  change (∑' i : {i | q i = a}, g (q i)) = _
  rw [hset]
  trans ∑ i ∈ D a, g (q i)
  · exact (D a).tsum_subtype (fun i => g (q i))
  · trans ∑ _i ∈ D a, g a
    · apply Finset.sum_congr rfl
      intro i hi
      rw [(hD i a).mp hi]
    · simp

theorem tsum_triple_patterns {I A : Type*} [DecidableEq A]
    (q : I → A) (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    (∑' t, f t) = ∑ p : TriplePattern,
      ∑' t : {t // classifyTriple (q ∘ t) = p}, f t := by
  simpa only [tsum_fintype] using
    tsum_regroup_occurrences (fun t => classifyTriple (q ∘ t)) f hf

theorem summable_reflectSlots {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (e : Fin 3 → Bool) (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    Summable (fun t => ‖f (reflectSlots r e t)‖) :=
  hf.comp_injective (reflectSlots_involutive r hr e).injective

theorem tsum_reflectSlots {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (e : Fin 3 → Bool) (f : (Fin 3 → I) → ℂ) (_hf : Summable (fun t => ‖f t‖)) :
    (∑' t, f (reflectSlots r e t)) = ∑' t, f t :=
  ((reflectSlots_involutive r hr e).toPerm _).tsum_eq f

theorem tsum_eight_reflections {I : Type*} (r : I → I) (hr : Function.Involutive r)
    (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    (∑' t, f t) = (1 / 8 : ℂ) *
      ∑ e : Fin 3 → Bool, ∑' t, f (reflectSlots r e t) := by
  simp_rw [tsum_reflectSlots r hr _ f hf]
  simp [Fintype.card_pi]

theorem tsum_reflectSlots_pattern {I A : Type*} [DecidableEq A]
    (r : I → I) (hr : Function.Involutive r) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (e : Fin 3 → Bool) (p : TriplePattern)
    (f : (Fin 3 → I) → ℂ) (_hf : Summable (fun t => ‖f t‖)) :
    (∑' t : {t // classifyTriple (q ∘ t) = p}, f (reflectSlots r e t)) =
      ∑' t : {t // classifyTriple (q ∘ t) = p}, f t := by
  let R : {t // classifyTriple (q ∘ t) = p} → {t // classifyTriple (q ∘ t) = p} :=
    fun t => ⟨reflectSlots r e t, (reflectSlots_pattern r q hq e t).trans t.property⟩
  have hR : Function.Involutive R := by
    intro t
    apply Subtype.ext
    exact reflectSlots_involutive r hr e t
  exact (hR.toPerm R).tsum_eq (fun t => f t.val)

theorem tsum_eight_reflections_pattern {I A : Type*} [DecidableEq A]
    (r : I → I) (hr : Function.Involutive r) (q : I → A)
    (hq : ∀ i, q (r i) = q i) (p : TriplePattern)
    (f : (Fin 3 → I) → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    (∑' t : {t // classifyTriple (q ∘ t) = p}, f t) = (1 / 8 : ℂ) *
      ∑ e : Fin 3 → Bool, ∑' t : {t // classifyTriple (q ∘ t) = p},
        f (reflectSlots r e t) := by
  simp_rw [tsum_reflectSlots_pattern r hr q hq _ p f hf]
  simp [Fintype.card_pi]

theorem dominated_occurrence_limit {I K : Type*} (l : Filter K)
    (f : K → I → ℂ) (g : I → ℂ) (B : I → ℝ) (hB : Summable B)
    (hlim : ∀ i, Tendsto (fun k => f k i) l (𝓝 (g i)))
    (hbound : ∀ᶠ k in l, ∀ i, ‖f k i‖ ≤ B i) :
    Tendsto (fun k => ∑' i, f k i) l (𝓝 (∑' i, g i)) :=
  tendsto_tsum_of_dominated_convergence hB hlim hbound

end HigherCorrelations
