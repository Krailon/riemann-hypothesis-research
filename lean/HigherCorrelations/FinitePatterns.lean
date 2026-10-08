import HigherCorrelations.FiniteDefinitions

/-! UNCONDITIONAL finite identities. All sums are over occurrences, not images. -/
namespace HigherCorrelations

theorem classifyTriple_iff {A : Type*} [DecidableEq A] (v : Fin 3 → A)
    (p : TriplePattern) : classifyTriple v = p ↔ HasPattern p v := by
  cases p <;> simp only [classifyTriple, HasPattern]
  all_goals split_ifs <;> simp_all <;> grind

theorem pattern_unique {A : Type*} [DecidableEq A] (v : Fin 3 → A) :
    ∃! p, HasPattern p v := by
  refine ⟨classifyTriple v, (classifyTriple_iff v _).mp rfl, ?_⟩
  intro p hp
  exact ((classifyTriple_iff v p).mpr hp).symm

theorem pattern_disjoint {A : Type*} [DecidableEq A] (v : Fin 3 → A)
    {p q : TriplePattern} (hpq : p ≠ q) : ¬ (HasPattern p v ∧ HasPattern q v) := by
  rintro ⟨hp, hq⟩
  exact hpq (((classifyTriple_iff v p).mpr hp).symm.trans
    ((classifyTriple_iff v q).mpr hq))

theorem sum_regroup_fibers {I A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (D : Finset I) (q : I → A) (f : I → M) :
    (∑ i ∈ D, f i) = ∑ a ∈ D.image q, ∑ i ∈ D.filter (fun i => q i = a), f i := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) f

theorem sum_regroup_multiplicity {I A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (D : Finset I) (q : I → A) (g : A → M) :
    (∑ i ∈ D, g (q i)) =
      ∑ a ∈ D.image q, (D.filter (fun i => q i = a)).card • g a := by
  rw [sum_regroup_fibers D q]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    _ = ∑ _i ∈ D.filter (fun i => q i = a), g a := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by simp

theorem sum_triple_patterns {I A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (q : I → A) (S : Fin 3 → Finset I) (f : (Fin 3 → I) → M) :
    (∑ t ∈ tripleDomain S, f t) =
      ∑ p : TriplePattern, ∑ t ∈ patternDomain q S p, f t := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun _ _ => Finset.mem_univ _) f

end HigherCorrelations
