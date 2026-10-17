import HigherCorrelations.PairDiagonalPNT
import HigherCorrelations.PairDiagonalAlgebra
import HigherCorrelations.PairSievePrimePowers

/-! UNCONDITIONAL. The squared Mangoldt cumulative sum has remainder O(u).
Constants inherited from the PNT are existential. -/
namespace HigherCorrelations
noncomputable section
open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

/-- The logarithmic Mangoldt moment differs from the squared moment only on
proper prime powers. The already checked finite power count bounds this loss. -/
theorem pairDiagonalCumulative_power_loss (u : ℝ) (hu : 1 ≤ u) :
    0 ≤ (∑ n ∈ Icc 0 ⌊u⌋₊, Λ n*Real.log n)-pairDiagonalCumulative u ∧
    (∑ n ∈ Icc 0 ⌊u⌋₊, Λ n*Real.log n)-pairDiagonalCumulative u ≤
      pairSievePowerConstant*u := by
  let N := ⌊u⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hu)
  have hNu : (N:ℝ) ≤ u := Nat.floor_le (by linarith)
  have he : (∑ n ∈ Icc 0 N, Λ n*Real.log n)-pairDiagonalCumulative u =
      ∑ n ∈ Icc 0 N, Λ n*(Real.log n-Λ n) := by
    unfold pairDiagonalCumulative
    rw [← sum_sub_distrib]
    apply sum_congr rfl; intro n hn; ring
  have hnon (n : ℕ) : 0 ≤ Λ n*(Real.log n-Λ n) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (sub_nonneg.mpr ArithmeticFunction.vonMangoldt_le_log)
  change 0 ≤ (∑ n ∈ Icc 0 N, Λ n*Real.log n)-pairDiagonalCumulative u ∧ _
  rw [he]
  refine ⟨sum_nonneg (fun n _ => hnon n), ?_⟩
  have hpoint (n : ℕ) (hn : n ∈ Icc 0 N) :
      Λ n*(Real.log n-Λ n) ≤
        if n ∈ pairSieveProperPowers N then (Real.log N)^2 else 0 := by
    by_cases hp : n.Prime
    · simp [ArithmeticFunction.vonMangoldt_apply_prime hp, pairSieveProperPowers, hp]
    by_cases hpp : IsPrimePow n
    · have hn0 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hpp.ne_zero
      have hm : n ∈ pairSieveProperPowers N := mem_filter.mpr
        ⟨mem_Icc.mpr ⟨hn0,(mem_Icc.mp hn).2⟩, hpp,hp⟩
      rw [if_pos hm]
      have hnR : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
      have hl : Real.log n ≤ Real.log N := Real.log_le_log hnR (by exact_mod_cast (mem_Icc.mp hn).2)
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hΛlog := ArithmeticFunction.vonMangoldt_le_log (n := n)
      have hlog := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
      nlinarith [mul_le_mul (hΛlog.trans hl) (sub_le_self (Real.log n) hΛ |>.trans hl)
        (sub_nonneg.mpr hΛlog) hlog]
    · have hz : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
      simp [hz, pairSieveProperPowers, hpp]
  calc
    _ ≤ ∑ n ∈ Icc 0 N, if n ∈ pairSieveProperPowers N then (Real.log N)^2 else 0 :=
      sum_le_sum hpoint
    _ = ((pairSieveProperPowers N).card:ℝ)*(Real.log N)^2 := by
      rw [← sum_filter]
      have hs : (Icc 0 N).filter (fun n => n ∈ pairSieveProperPowers N) = pairSieveProperPowers N := by
        ext n
        constructor
        · intro hn; exact (mem_filter.mp hn).2
        · intro hn
          have hni := (mem_filter.mp hn).1
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, (mem_Icc.mp hni).2⟩, hn⟩
      rw [hs, sum_const, nsmul_eq_mul]
    _ ≤ pairSievePowerConstant*N := pairSieveProperPowers_weighted N hN
    _ ≤ pairSievePowerConstant*u := mul_le_mul_of_nonneg_left hNu pairSievePowerConstant_pos.le

/-- Finite Abel summation, before any infinite-tail limit. -/
theorem pairDiagonal_log_moment (u : ℝ) (hu : 1 ≤ u) :
    (∑ n ∈ Icc 0 ⌊u⌋₊, Λ n*Real.log n) =
      Real.log u*Chebyshev.psi u-∫ t in (1:ℝ)..u, Chebyshev.psi t/t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 u) : DifferentiableAt ℝ Real.log t :=
    Real.differentiableAt_log (by linarith [ht.1])
  have hi : IntegrableOn (deriv Real.log) (Set.Icc 1 u) := by
    have he : Set.EqOn (deriv Real.log) (fun t : ℝ => t⁻¹) (Set.Icc 1 u) :=
      fun t _ => Real.deriv_log t
    exact ((continuousOn_id.inv₀ (fun t ht => by dsimp; linarith [ht.1])).integrableOn_Icc).congr_fun
      (fun t ht => (he ht).symm) measurableSet_Icc
  have he := sum_mul_eq_sub_integral_mul₀ (fun n : ℕ => Λ n) (f := Real.log) (by simp) u hd hi
  simp only [← Chebyshev.psi_eq_sum_Icc, Real.deriv_log] at he
  rw [← intervalIntegral.integral_of_le hu] at he
  convert he using 1
  · apply sum_congr rfl; intro n hn; ring
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    ring

/-- The moment error is bounded uniformly on the entire real half-line u>=1. -/
theorem pairDiagonalCumulative_bound : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 ≤ u →
    |pairDiagonalCumulative u-u*Real.log u| ≤ C*u := by
  obtain ⟨K,hK,hKbound⟩ := pairDiagonalPNT_log_error
  let B := Real.log 4+4
  have hB : 0 < B := by dsimp [B]; positivity
  have hppC := pairSievePowerConstant_pos
  refine ⟨K+B+pairSievePowerConstant, by positivity, ?_⟩
  intro u hu
  have hlog := Real.log_nonneg hu
  have herr := hKbound u hu
  have hpp := pairDiagonalCumulative_power_loss u hu
  have hint : |∫ t in (1:ℝ)..u, Chebyshev.psi t/t| ≤ B*u := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := B)
      (f := fun t : ℝ => Chebyshev.psi t/t) (a := 1) (b := u) (by
        intro t ht
        rw [Set.uIoc_of_le hu] at ht
        have ht0 : 0 < t := by linarith [ht.1]
        rw [Real.norm_of_nonneg (div_nonneg (Chebyshev.psi_nonneg _) ht0.le)]
        exact (div_le_iff₀ ht0).mpr (Chebyshev.psi_le_const_mul_self ht0.le))
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ u-1)] at hb
    exact hb.trans (by nlinarith)
  have hid := pairDiagonal_log_moment u hu
  have hmul : |Real.log u*(Chebyshev.psi u-u)| ≤ K*u := by
    rw [abs_mul, abs_of_nonneg hlog, mul_comm]; exact herr
  have hcomb := abs_sub (Real.log u*(Chebyshev.psi u-u))
    (∫ t in (1:ℝ)..u, Chebyshev.psi t/t)
  have hlogerr : |(∑ n ∈ Icc 0 ⌊u⌋₊, Λ n*Real.log n)-u*Real.log u| ≤ (K+B)*u := by
    rw [hid]
    have he : Real.log u*Chebyshev.psi u-(∫ t in (1:ℝ)..u, Chebyshev.psi t/t)-u*Real.log u =
        Real.log u*(Chebyshev.psi u-u)-(∫ t in (1:ℝ)..u, Chebyshev.psi t/t) := by ring
    rw [he]; nlinarith
  have hh := abs_sub_le (pairDiagonalCumulative u)
    (∑ n ∈ Icc 0 ⌊u⌋₊, Λ n*Real.log n) (u*Real.log u)
  have he : |pairDiagonalCumulative u-(∑ n ∈ Icc 0 ⌊u⌋₊, Λ n*Real.log n)| ≤
      pairSievePowerConstant*u := by rw [abs_sub_comm, abs_of_nonneg hpp.1]; exact hpp.2
  nlinarith

end
end HigherCorrelations
