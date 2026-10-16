import HigherCorrelations.PairSieveCount
import HigherCorrelations.PairSieveGeometry

/-! UNCONDITIONAL. Finite ball majorants in the existing zero-based prime
indexing. Each row is finitely supported; its sum is bounded by the sieve count. -/
namespace HigherCorrelations
noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt

theorem pairSieveNearbyConstant_pos : 0 < pairSieveNearbyConstant := by
  unfold pairSieveNearbyConstant
  have := pairSieveCountConstant_pos
  positivity

theorem pairSieveBall_nonneg (X δ R : ℝ) (hR : 0 ≤ R) (p : ℕ × ℕ) :
    0 ≤ pairSieveBall X δ R p := by
  unfold pairSieveBall
  split_ifs
  · exact mul_nonneg (by positivity) (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)
  · rfl

theorem pairSieveBall_support (X δ R : ℝ) (p : ℕ × ℕ)
    (hp : p ∉ range ⌊R⌋₊ ×ˢ range ⌊R⌋₊) : pairSieveBall X δ R p = 0 := by
  unfold pairSieveBall
  apply ite_eq_right
  intro he
  obtain ⟨h12,_⟩ := mem_filter.mp he
  obtain ⟨h1,h2⟩ := mem_product.mp h12
  apply hp
  simp only [mem_product, mem_range]
  have := (mem_Icc.mp h1).2
  have := (mem_Icc.mp h2).2
  omega

theorem pairSieveBall_summable (X δ R : ℝ) : Summable (pairSieveBall X δ R) :=
  summable_of_ne_finset_zero (pairSieveBall_support X δ R)

theorem pairSieveBall_bound (X δ R : ℝ) (hδ : 0 ≤ δ) (hR : 0 < R) :
    (∑' p, pairSieveBall X δ R p) ≤ (pairSieveNearbyConstant/2)*δ*X^2/R := by
  let S := (range ⌊R⌋₊ ×ˢ range ⌊R⌋₊).filter
    (fun p => (p.1+1,p.2+1) ∈ pairSieveNearby R (2*Real.pi*δ*R))
  have he : (∑' p, pairSieveBall X δ R p) =
      (8*(Real.exp Real.pi)^3*X^2/R^3)*(∑ p ∈ S, Λ (p.1+1)*Λ (p.2+1)) := by
    rw [tsum_eq_sum (pairSieveBall_support X δ R), mul_sum]
    unfold pairSieveBall
    rw [← sum_filter]
  have hc : (∑ p ∈ S, Λ (p.1+1)*Λ (p.2+1)) ≤
      ∑ p ∈ pairSieveNearby R (2*Real.pi*δ*R), Λ p.1*Λ p.2 := by
    apply sum_le_sum_of_injOn (fun p : ℕ × ℕ => (p.1+1,p.2+1))
    · intro a ha b hb hab
      have h1 := congrArg Prod.fst hab
      have h2 := congrArg Prod.snd hab
      apply Prod.ext <;> dsimp at * <;> omega
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
      exact (mem_filter.mp ha).2
    · intro p hp; rfl
    · intro p hp _
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  have hcount := pairSieveNearby_bound R (2*Real.pi*δ*R) hR.le (by positivity)
  rw [he]
  calc
    _ ≤ (8*(Real.exp Real.pi)^3*X^2/R^3)*(pairSieveCountConstant*R*(2*Real.pi*δ*R)) :=
      mul_le_mul_of_nonneg_left (hc.trans hcount) (by positivity)
    _ = _ := by unfold pairSieveNearbyConstant; field_simp; ring

theorem pairSieveBall_dyadic_bound (X δ : ℝ) (hX : 0 < X) (hδ : 0 ≤ δ) (j : ℕ) :
    (∑' p, pairSieveBall X δ ((2:ℝ)^j*X) p) ≤
      ((pairSieveNearbyConstant/2)*δ*X)*(1/2:ℝ)^j := by
  apply (pairSieveBall_bound X δ _ hδ (by positivity)).trans
  apply le_of_eq
  rw [one_div_pow]
  field_simp
end
end HigherCorrelations
