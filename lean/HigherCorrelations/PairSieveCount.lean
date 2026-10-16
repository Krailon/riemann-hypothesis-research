import HigherCorrelations.PairSieveShiftCount

/-! UNCONDITIONAL. Ordered Mangoldt pair counts with inclusive height and
inclusive distance cutoffs; real cutoffs are translated by natural floors. -/
namespace HigherCorrelations
noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt

/-- The positive orientation is exactly parametrized by a positive shift. -/
theorem pairSievePositivePairs_sum (U V : ℕ) :
    (∑ p ∈ pairSievePositivePairs U V, Λ p.1*Λ p.2) =
      ∑ h ∈ Icc 1 V, pairSieveShiftMangoldt U h := by
  have he : (∑ p ∈ pairSievePositivePairs U V, Λ p.1*Λ p.2) =
      ∑ p ∈ ((Icc 1 V) ×ˢ (Icc 1 U)).filter (fun p => p.2+p.1 ≤ U),
        Λ p.2*Λ (p.2+p.1) := by
    apply sum_bij (fun p _ => (p.2-p.1,p.1))
    · intro p hp
      simp only [pairSievePositivePairs, mem_filter, mem_product, mem_Icc] at hp ⊢
      omega
    · intro a ha b hb hab
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      have h1 := congrArg Prod.fst hab
      have h2 := congrArg Prod.snd hab
      apply Prod.ext <;> dsimp at * <;> omega
    · intro p hp
      refine ⟨(p.2,p.2+p.1), ?_, ?_⟩
      · simp only [pairSievePositivePairs, mem_filter, mem_product, mem_Icc] at hp ⊢
        omega
      · simp
    · intro p hp
      have hp' := (mem_filter.mp hp).2
      dsimp
      rw [Nat.add_sub_of_le hp'.1.le]
  rw [he, sum_filter, sum_product]
  rfl

/-- Both orientations occur, with no diagonal and no multiplicity division. -/
theorem pairSieveNearbyNat_sum (U V : ℕ) :
    (∑ p ∈ pairSieveNearbyNat U V, Λ p.1*Λ p.2) =
      2*∑ h ∈ Icc 1 V, pairSieveShiftMangoldt U h := by
  let A := (Icc 1 U) ×ˢ (Icc 1 U)
  let f : ℕ × ℕ → ℝ := fun p => if p.1 < p.2 ∧ p.2-p.1 ≤ V then Λ p.1*Λ p.2 else 0
  have he : (∑ p ∈ pairSieveNearbyNat U V, Λ p.1*Λ p.2) =
      (∑ p ∈ A, f p)+(∑ p ∈ A, f p.swap) := by
    rw [← sum_add_distrib]
    unfold pairSieveNearbyNat
    rw [sum_filter]
    apply sum_congr rfl; intro p hp
    dsimp [f]
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · rw [Nat.dist_eq_sub_of_le hlt.le]
      have hne := ne_of_lt hlt
      simp [hlt, hne, not_lt_of_ge hlt.le]
    · simp [heq]
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hgt.le]
      have hne := ne_of_gt hgt
      simp [hgt, hne, not_lt_of_ge hgt.le, mul_comm]
  have hswap : (∑ p ∈ A, f p.swap) = ∑ p ∈ A, f p := by
    apply sum_bij (fun p _ => p.swap)
    · intro p hp; simpa only [A, mem_product, Prod.swap, and_comm] using hp
    · intro a ha b hb hab; exact Prod.swap_injective hab
    · intro p hp; exact ⟨p.swap, by simpa only [A, mem_product, Prod.swap, and_comm] using hp, by simp⟩
    · intro p hp; rfl
  have hpos : (∑ p ∈ A, f p) = ∑ h ∈ Icc 1 V, pairSieveShiftMangoldt U h := by
    rw [← pairSievePositivePairs_sum]
    unfold pairSievePositivePairs
    rw [sum_filter]
  rw [he, hswap, hpos]
  ring

theorem pairSieveNearbyNat_bound (U V : ℕ) :
    (∑ p ∈ pairSieveNearbyNat U V, Λ p.1*Λ p.2) ≤ pairSieveCountConstant*U*V := by
  by_cases hU : 2 ≤ U
  · rw [pairSieveNearbyNat_sum]
    have := pairSieveShiftMangoldt_sum_le U V hU
    linarith
  · have he : pairSieveNearbyNat U V = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      simp only [pairSieveNearbyNat, mem_filter, mem_product, mem_Icc] at hp
      omega
    rw [he, sum_empty]
    have := pairSieveCountConstant_pos
    positivity

/-- Absolute real distance equals the natural distance, including either order. -/
theorem pairSieve_dist_cast (m n : ℕ) : (Nat.dist m n : ℝ) = |(m : ℝ)-n| := by
  rcases le_total m n with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

/-- The real cutoff is inclusive and uses floor, including V=0. -/
theorem pairSieveNearby_eq (U V : ℝ) (hV : 0 ≤ V) :
    pairSieveNearby U V = pairSieveNearbyNat ⌊U⌋₊ ⌊V⌋₊ := by
  unfold pairSieveNearby pairSieveNearbyNat
  apply filter_congr; intro p hp
  rw [← pairSieve_dist_cast, Nat.le_floor_iff hV]

theorem pairSieveNearby_bound (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (∑ p ∈ pairSieveNearby U V, Λ p.1*Λ p.2) ≤ pairSieveCountConstant*U*V := by
  rw [pairSieveNearby_eq U V hV]
  apply (pairSieveNearbyNat_bound ⌊U⌋₊ ⌊V⌋₊).trans
  have hC := pairSieveCountConstant_pos
  gcongr
  · exact Nat.floor_le hU
  · exact Nat.floor_le hV

/-- A subunit gap contains no distinct integer pairs. -/
theorem pairSieveNearby_empty (U V : ℝ) (hV : V < 1) : pairSieveNearby U V = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hp' := (mem_filter.mp hp).2
  rw [← pairSieve_dist_cast] at hp'
  have hdist : 1 ≤ Nat.dist p.1 p.2 := Nat.one_le_iff_ne_zero.mpr
    (fun he => hp'.1 (Nat.eq_of_dist_eq_zero he))
  have : (1 : ℝ) ≤ (Nat.dist p.1 p.2 : ℝ) := by exact_mod_cast hdist
  linarith [hp'.2]
end
end HigherCorrelations
