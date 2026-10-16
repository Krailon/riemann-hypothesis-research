import HigherCorrelations.PairSieveCutoff
import HigherCorrelations.PairSievePrimePowers

/-! UNCONDITIONAL. Averaged positive-shift Mangoldt count, with prime and proper
prime-power terms separately bounded. The reverse orientation is added later. -/
namespace HigherCorrelations
noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt

theorem pairSieveCountConstant_pos : 0 < pairSieveCountConstant := by
  unfold pairSieveCountConstant
  have := pairSievePrimeConstant_pos
  have := pairSievePowerConstant_pos
  positivity

theorem pairSieve_odd_card (U h : ℕ) (hh0 : 0 < h) (hh : ¬2 ∣ h) :
    (pairSievePrimes U h).card ≤ 1 := by
  have hs : pairSievePrimes U h ⊆ {2} := by
    intro n hn
    obtain ⟨_, hnp, hnhp⟩ := mem_filter.mp hn
    have hn := hnp.eq_two_or_odd
    have hnh := hnhp.eq_two_or_odd
    have hn2 := hnp.two_le
    rw [Nat.dvd_iff_mod_eq_zero] at hh
    simp only [mem_singleton]
    omega
  simpa using card_le_card hs

/-- The proper-power contribution is covered in both coordinates. -/
theorem pairSieveActive_subset (U h : ℕ) :
    pairSieveActive U h ⊆ pairSievePrimes U h ∪
      (pairSieveProperPowers U ∪ (pairSieveProperPowers U).image (fun n => n-h)) := by
  intro n hn
  obtain ⟨hnI, hnU, hnpp, hnhpp⟩ := mem_filter.mp hn
  by_cases hnp : n.Prime
  · by_cases hnhp : (n+h).Prime
    · exact mem_union_left _ (mem_filter.mpr ⟨hnI, hnp, hnhp⟩)
    · apply mem_union_right
      apply mem_union_right
      exact mem_image.mpr ⟨n+h, mem_filter.mpr
        ⟨mem_Icc.mpr ⟨by have := (mem_Icc.mp hnI).1; omega, hnU⟩, hnhpp, hnhp⟩,
        Nat.add_sub_cancel n h⟩
  · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hnI, hnpp, hnp⟩))

theorem pairSieveActive_card (U h : ℕ) :
    (pairSieveActive U h).card ≤ (pairSievePrimes U h).card+2*(pairSieveProperPowers U).card := by
  have ha := card_le_card (pairSieveActive_subset U h)
  have hb := card_union_le (pairSievePrimes U h)
    (pairSieveProperPowers U ∪ (pairSieveProperPowers U).image (fun n => n-h))
  have hc := card_union_le (pairSieveProperPowers U) ((pairSieveProperPowers U).image (fun n => n-h))
  have hd := card_image_le (s := pairSieveProperPowers U) (f := fun n => n-h)
  omega

theorem pairSieveShiftMangoldt_active (U h : ℕ) :
    pairSieveShiftMangoldt U h = ∑ n ∈ pairSieveActive U h, Λ n*Λ (n+h) := by
  unfold pairSieveShiftMangoldt pairSieveActive
  rw [sum_filter]
  apply sum_congr rfl; intro n hn
  by_cases hcut : n+h ≤ U
  · by_cases hnpp : IsPrimePow n
    · by_cases hnhpp : IsPrimePow (n+h)
      · simp [hcut, hnpp, hnhpp]
      · simp [hcut, hnhpp, ArithmeticFunction.vonMangoldt_apply]
    · simp [hcut, hnpp, ArithmeticFunction.vonMangoldt_apply]
  · simp [hcut]

theorem pairSieveShiftMangoldt_le (U h : ℕ) :
    pairSieveShiftMangoldt U h ≤
      (((pairSievePrimes U h).card : ℝ)+2*(pairSieveProperPowers U).card)*Real.log U^2 := by
  rw [pairSieveShiftMangoldt_active]
  calc
    _ ≤ ∑ _n ∈ pairSieveActive U h, Real.log U^2 := by
      apply sum_le_sum; intro n hn
      obtain ⟨hnI, hnU, _, _⟩ := mem_filter.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
      have hnh0 : (0 : ℝ) < (n+h : ℕ) := by
        exact_mod_cast (show 0 < n+h by have := (mem_Icc.mp hnI).1; omega)
      have hln : Λ n ≤ Real.log U := ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log hn0 (by exact_mod_cast (mem_Icc.mp hnI).2))
      have hlnh : Λ (n+h) ≤ Real.log U := ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log hnh0 (by exact_mod_cast hnU))
      simpa [pow_two] using mul_le_mul hln hlnh ArithmeticFunction.vonMangoldt_nonneg
        (ArithmeticFunction.vonMangoldt_nonneg.trans hln)
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast pairSieveActive_card U h

theorem pairSieve_log_sq_le (U : ℝ) (hU : 1 ≤ U) : Real.log U^2 ≤ 4*U := by
  have hl := Real.log_le_rpow_div (by linarith : 0 ≤ U) (show (0 : ℝ)<1/2 by norm_num)
  have hl' : Real.log U ≤ 2*U^(1/2:ℝ) := by linarith
  have he := pow_le_pow_left₀ (Real.log_nonneg hU) hl' 2
  rw [mul_pow, ← Real.rpow_natCast (U^(1/2:ℝ)), ← Real.rpow_mul (by linarith : 0 ≤ U)] at he
  norm_num at he ⊢; exact he

/-- All positive shifts, including odd ones, with a uniform additive allowance. -/
theorem pairSieve_prime_bound_all (U h : ℕ) (hU : 2 ≤ U) (hh : 0 < h) :
    ((pairSievePrimes U h).card : ℝ)*Real.log U^2 ≤
      pairSievePrimeConstant*pairSieveBadFactor h*U+4*U := by
  by_cases heven : 2 ∣ h
  · have := pairSieve_prime_bound U h hU heven (by omega)
    have : (0 : ℝ) ≤ U := by positivity
    linarith [pairSieve_prime_bound U h hU heven (by omega)]
  · have hc : ((pairSievePrimes U h).card : ℝ) ≤ 1 := by exact_mod_cast pairSieve_odd_card U h hh heven
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log U))
    have hl := pairSieve_log_sq_le U (by exact_mod_cast (show 1 ≤ U by omega))
    have hnon : 0 ≤ pairSievePrimeConstant*pairSieveBadFactor h*U := by
      have := pairSievePrimeConstant_pos
      have := pairSieveBadFactor_one_le h
      positivity
    nlinarith

/-- The averaged positive-shift bound, uniform even when V exceeds U. -/
theorem pairSieveShiftMangoldt_sum_le (U V : ℕ) (hU : 2 ≤ U) :
    (∑ h ∈ Icc 1 V, pairSieveShiftMangoldt U h) ≤
      (pairSieveCountConstant/2)*U*V := by
  have hp := pairSieveProperPowers_weighted U (by omega)
  have hs : (∑ h ∈ Icc 1 V, pairSieveShiftMangoldt U h) ≤
      ∑ h ∈ Icc 1 V, (pairSievePrimeConstant*pairSieveBadFactor h*U+
        (4+2*pairSievePowerConstant)*U) := by
    apply sum_le_sum; intro h hh
    have hbound := pairSieveShiftMangoldt_le U h
    have hprime := pairSieve_prime_bound_all U h hU (mem_Icc.mp hh).1
    nlinarith
  have he : (∑ h ∈ Icc 1 V, (pairSievePrimeConstant*pairSieveBadFactor h*U+
        (4+2*pairSievePowerConstant)*U)) =
      pairSievePrimeConstant*U*(∑ h ∈ Icc 1 V, pairSieveBadFactor h)+
        (4+2*pairSievePowerConstant)*U*V := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    simp only [Nat.card_Icc, Nat.add_sub_cancel, mul_sum]
    congr 1
    · apply sum_congr rfl; intro h hh; ring
    · ring
  rw [he] at hs
  have hm := mul_le_mul_of_nonneg_left (pairSieveBadFactor_sum_le V)
    (show 0 ≤ pairSievePrimeConstant*(U : ℝ) by have := pairSievePrimeConstant_pos; positivity)
  unfold pairSieveCountConstant
  nlinarith
end
end HigherCorrelations
