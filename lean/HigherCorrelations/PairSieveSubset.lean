import HigherCorrelations.PairSieveDefinitions
import Mathlib

/-! UNCONDITIONAL. Finite, nonnegative subset sums used to bound the sieve
normalizer. All sums here are finite; no Euler-product limit is implicit. -/
namespace HigherCorrelations
noncomputable section
open Finset

/-- Union convolution of two product measures on subsets. -/
theorem pairSieve_subset_union {α : Type*} [DecidableEq α] (s : Finset α)
    (u v : α → ℝ) (F : Finset α → ℝ) :
    (∑ a ∈ s.powerset, ∑ b ∈ s.powerset,
      pairSieveWeight u a * pairSieveWeight v b * F (a ∪ b)) =
    ∑ d ∈ s.powerset, pairSieveWeight (fun p => u p + v p + u p*v p) d * F d := by
  induction s using Finset.induction_on generalizing F with
  | empty => simp [pairSieveWeight]
  | @insert p s hp ih =>
    have hpa : ∀ a ∈ s.powerset, p ∉ a := fun a ha h => hp ((mem_powerset.mp ha) h)
    have hw (w : α → ℝ) (a : Finset α) (ha : a ∈ s.powerset) :
        pairSieveWeight w (insert p a) = w p * pairSieveWeight w a := by
      exact prod_insert (hpa a ha)
    let B := ∑ a ∈ s.powerset, ∑ b ∈ s.powerset,
      pairSieveWeight u a * pairSieveWeight v b * F (insert p (a ∪ b))
    have h1 : (∑ a ∈ s.powerset, ∑ b ∈ s.powerset,
        pairSieveWeight u a * pairSieveWeight v (insert p b) * F (a ∪ insert p b)) =
        v p * B := by
      dsimp [B]
      simp only [mul_sum]
      apply sum_congr rfl; intro a ha
      apply sum_congr rfl; intro b hb
      rw [hw v b hb, union_insert]
      ring
    have h2 : (∑ a ∈ s.powerset, ∑ b ∈ s.powerset,
        pairSieveWeight u (insert p a) * pairSieveWeight v b * F (insert p a ∪ b)) =
        u p * B := by
      dsimp [B]
      simp only [mul_sum]
      apply sum_congr rfl; intro a ha
      apply sum_congr rfl; intro b hb
      rw [hw u a ha, insert_union]
      ring
    have h3 : (∑ a ∈ s.powerset, ∑ b ∈ s.powerset,
        pairSieveWeight u (insert p a) * pairSieveWeight v (insert p b) *
          F (insert p a ∪ insert p b)) = u p * v p * B := by
      dsimp [B]
      simp only [mul_sum]
      apply sum_congr rfl; intro a ha
      apply sum_congr rfl; intro b hb
      rw [hw u a ha, hw v b hb, insert_union, union_insert, insert_idem]
      ring
    have h4 : (∑ d ∈ s.powerset,
        pairSieveWeight (fun q => u q+v q+u q*v q) (insert p d) * F (insert p d)) =
        (u p+v p+u p*v p) * B := by
      dsimp [B]
      rw [ih (fun d => F (insert p d)), mul_sum]
      apply sum_congr rfl; intro d hd
      rw [hw _ d hd]
      ring
    simp only [sum_powerset_insert hp, sum_add_distrib]
    rw [h1, h2, h3, h4, ih]
    ring

/-- Marginalizing the discarded primes gives a finite Euler factor. -/
theorem pairSieve_subset_filter {α : Type*} [DecidableEq α] (s : Finset α)
    (w : α → ℝ) (q : α → Prop) [DecidablePred q] (F : Finset α → ℝ) :
    (∑ a ∈ s.powerset, pairSieveWeight w a * F (a.filter q)) =
    (∏ p ∈ s.filter (fun p => ¬q p), (1+w p)) *
      ∑ a ∈ (s.filter q).powerset, pairSieveWeight w a * F a := by
  induction s using Finset.induction_on generalizing F with
  | empty => simp [pairSieveWeight]
  | @insert p s hp ih =>
    have hpa : ∀ a ∈ s.powerset, p ∉ a := fun a ha h => hp ((mem_powerset.mp ha) h)
    have hw (a : Finset α) (ha : a ∈ s.powerset) :
        pairSieveWeight w (insert p a) = w p * pairSieveWeight w a :=
      prod_insert (hpa a ha)
    have hpq : p ∉ s.filter q := fun h => hp (mem_filter.mp h).1
    have hpn : p ∉ s.filter (fun p => ¬q p) := fun h => hp (mem_filter.mp h).1
    rw [sum_powerset_insert hp]
    by_cases hq : q p
    · simp only [filter_insert, hq, not_true_eq_false, ite_false, ite_true]
      have he : (∑ a ∈ s.powerset,
          pairSieveWeight w (insert p a) * F (insert p (a.filter q))) =
          w p * ∑ a ∈ s.powerset, pairSieveWeight w a * F (insert p (a.filter q)) := by
        rw [mul_sum]; apply sum_congr rfl; intro a ha
        rw [hw a ha]; ring
      rw [he, ih, ih (fun a => F (insert p a)), sum_powerset_insert hpq]
      have he' : (∑ a ∈ (s.filter q).powerset,
          pairSieveWeight w (insert p a) * F (insert p a)) =
          w p * ∑ a ∈ (s.filter q).powerset, pairSieveWeight w a * F (insert p a) := by
        rw [mul_sum]; apply sum_congr rfl; intro a ha
        have hap : a ∈ s.powerset := mem_powerset.mpr
          ((mem_powerset.mp ha).trans (filter_subset _ _))
        rw [hw a hap]; ring
      rw [he']; ring
    · simp only [filter_insert, hq, not_false_eq_true, ite_true, ite_false, prod_insert hpn]
      have he : (∑ a ∈ s.powerset, pairSieveWeight w (insert p a) * F (a.filter q)) =
          w p * ∑ a ∈ s.powerset, pairSieveWeight w a * F (a.filter q) := by
        rw [mul_sum]; apply sum_congr rfl; intro a ha
        rw [hw a ha]; ring
      rw [he, ih]; ring

theorem pairSieveSubsetSum_nonneg (s : Finset ℕ) (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ p ∈ s, 0 ≤ w p) : 0 ≤ pairSieveSubsetSum s w N := by
  apply sum_nonneg; intro a ha
  split_ifs
  · exact prod_nonneg (fun p hp => hw p ((mem_powerset.mp ha) hp))
  · rfl

/-- Squaring a truncated sum is controlled by union convolution, after
marginalizing any prescribed bad primes. -/
theorem pairSieveSubsetSum_sq_le (s : Finset ℕ) (w : ℕ → ℝ) (N : ℕ)
    (hs : ∀ p ∈ s, 1 ≤ p) (hw : ∀ p ∈ s, 0 ≤ w p)
    (q : ℕ → Prop) [DecidablePred q] :
    pairSieveSubsetSum s w N ^ 2 ≤
      (∏ p ∈ s.filter (fun p => ¬q p), (1+w p)^2) *
        pairSieveSubsetSum (s.filter q) (fun p => 2*w p+w p^2) (N^2) := by
  let F : Finset ℕ → ℝ := fun a => if (∏ p ∈ a, p) ≤ N^2 then 1 else 0
  have he : pairSieveSubsetSum s w N ^ 2 ≤
      ∑ a ∈ s.powerset, ∑ b ∈ s.powerset,
        pairSieveWeight w a * pairSieveWeight w b * F ((a ∪ b).filter q) := by
    unfold pairSieveSubsetSum
    rw [pow_two, sum_mul]
    simp only [mul_sum]
    apply sum_le_sum; intro a ha
    apply sum_le_sum; intro b hb
    have hwa : 0 ≤ pairSieveWeight w a := prod_nonneg
      (fun p hp => hw p ((mem_powerset.mp ha) hp))
    have hwb : 0 ≤ pairSieveWeight w b := prod_nonneg
      (fun p hp => hw p ((mem_powerset.mp hb) hp))
    have hF : 0 ≤ F ((a ∪ b).filter q) := by dsimp [F]; split_ifs <;> norm_num
    by_cases haN : (∏ p ∈ a, p) ≤ N
    · by_cases hbN : (∏ p ∈ b, p) ≤ N
      · have hun : ∀ p ∈ a ∪ b, 1 ≤ p := by
          intro p hp; rcases mem_union.mp hp with hp | hp
          · exact hs p ((mem_powerset.mp ha) hp)
          · exact hs p ((mem_powerset.mp hb) hp)
        have hf : (∏ p ∈ (a ∪ b).filter q, p) ≤ ∏ p ∈ a ∪ b, p :=
          prod_le_prod_of_subset_of_one_le (filter_subset _ _) (fun p hp _ => hun p hp)
        have hi : 1 ≤ ∏ p ∈ a ∩ b, p := one_le_prod (fun p hp => hun p (mem_union_left _ (mem_inter.mp hp).1))
        have hp : (∏ p ∈ a ∪ b, p) ≤ (∏ p ∈ a, p)*(∏ p ∈ b, p) := by
          calc _ ≤ (∏ p ∈ a ∪ b, p)*(∏ p ∈ a ∩ b, p) := Nat.le_mul_of_pos_right _ hi
               _ = _ := prod_union_inter
        have hN : (∏ p ∈ (a ∪ b).filter q, p) ≤ N^2 :=
          hf.trans (hp.trans (by simpa [pow_two] using Nat.mul_le_mul haN hbN))
        simp [haN, hbN, F, hN]
      · simp only [ite_eq_right hbN, mul_zero]
        positivity
    · simp only [ite_eq_right haN, zero_mul]
      positivity
  apply he.trans
  rw [pairSieve_subset_union s w w (fun a => F (a.filter q)),
    pairSieve_subset_filter s (fun p => w p+w p+w p*w p) q F]
  have hc : (fun p => w p+w p+w p*w p) = (fun p => 2*w p+w p^2) := by funext p; ring
  rw [hc]
  have hc' : (fun p => 1+(w p+w p+w p*w p)) = (fun p => (1+w p)^2) := by funext p; ring
  rw [hc']
  apply le_of_eq
  congr 1
  apply sum_congr rfl; intro a ha
  dsimp [F]
  split_ifs <;> simp

end
end HigherCorrelations
