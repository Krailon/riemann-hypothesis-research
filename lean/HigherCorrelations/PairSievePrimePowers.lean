import HigherCorrelations.PairSieveLinear
import PrimeNumberTheoremAnd.BrunTitchmarsh
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! UNCONDITIONAL. Proper prime powers in the inclusive interval [1,U].
The explicit constants retain the prime-two logarithm. -/
namespace HigherCorrelations
noncomputable section
open Finset

theorem pairSievePowerConstant_pos : 0 < pairSievePowerConstant := by
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold pairSievePowerConstant
  positivity

/-- The strict-range library enumeration is applied at U+1, preserving the
inclusive endpoint at U and all proper prime powers there. -/
theorem pairSieveProperPowers_card (U : ℕ) :
    ((pairSieveProperPowers U).card : ℝ) ≤
      (U+1:ℝ)^(1/2:ℝ)*(1+Real.log (U+1:ℝ)/Real.log 2) := by
  have hs : pairSieveProperPowers U ⊆
      ((Ico 1 (Nat.ceil (Real.sqrt (U+1)))) ×ˢ range (Nat.log 2 (U+1)+1)).image
        (fun p => p.1^p.2) := by
    intro n hn
    obtain ⟨hnI, hnpp, hnp⟩ := mem_filter.mp hn
    have hnrange : n ∈ (range (U+1)).filter IsPrimePow :=
      mem_filter.mpr ⟨mem_range.mpr (by have := (mem_Icc.mp hnI).2; omega), hnpp⟩
    have he := BrunTitchmarsh.range_filter_isPrimePow_subset_union (U+1) hnrange
    rcases mem_union.mp he with he | he
    · exact False.elim (hnp (mem_filter.mp he).2)
    · simpa only [Nat.cast_add, Nat.cast_one] using he
  have hc := (Nat.cast_le (α := ℝ)).mpr (card_le_card hs)
  exact hc.trans (by simpa only [Nat.cast_add, Nat.cast_one] using BrunTitchmarsh.pows_small_primes_le (U+1))

/-- Polynomial absorption of the entire logarithm-weighted proper-power count. -/
theorem pairSieveProperPowers_weighted (U : ℕ) (hU : 1 ≤ U) :
    ((pairSieveProperPowers U).card : ℝ)*Real.log U^2 ≤ pairSievePowerConstant*U := by
  let w : ℝ := U+1
  have hw : 1 ≤ w := by dsimp [w]; linarith [Nat.cast_nonneg (α := ℝ) U]
  have hw0 : 0 < w := by linarith
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hl0 : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU)
  have hlw : Real.log U ≤ Real.log w := Real.log_le_log hU0 (by dsimp [w]; linarith)
  have hlw0 := Real.log_nonneg hw
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log w ≤ 8*w^(1/8:ℝ) := by
    have := Real.log_le_rpow_div hw0.le (show (0 : ℝ)<1/8 by norm_num)
    linarith
  have hL2 : Real.log w^2 ≤ 64*w^(1/4:ℝ) := by
    have he := pow_le_pow_left₀ hlw0 hlog 2
    rw [mul_pow, ← Real.rpow_natCast (w^(1/8:ℝ)), ← Real.rpow_mul hw0.le] at he
    norm_num at he ⊢; exact he
  have hL3 : Real.log w^3 ≤ 512*w^(3/8:ℝ) := by
    have he := pow_le_pow_left₀ hlw0 hlog 3
    rw [mul_pow, ← Real.rpow_natCast (w^(1/8:ℝ)), ← Real.rpow_mul hw0.le] at he
    norm_num at he ⊢; exact he
  have hterm2 : w^(1/2:ℝ)*Real.log w^2 ≤ 64*w := by
    calc
      _ ≤ w^(1/2:ℝ)*(64*w^(1/4:ℝ)) := by gcongr
      _ = 64*w^(3/4:ℝ) := by
        rw [show (3/4:ℝ)=1/2+1/4 by norm_num, Real.rpow_add hw0]; ring
      _ ≤ _ := by gcongr; simpa using Real.rpow_le_rpow_of_exponent_le hw (show (3/4:ℝ)≤1 by norm_num)
  have hterm3 : w^(1/2:ℝ)*Real.log w^3 ≤ 512*w := by
    calc
      _ ≤ w^(1/2:ℝ)*(512*w^(3/8:ℝ)) := by gcongr
      _ = 512*w^(7/8:ℝ) := by
        rw [show (7/8:ℝ)=1/2+3/8 by norm_num, Real.rpow_add hw0]; ring
      _ ≤ _ := by gcongr; simpa using Real.rpow_le_rpow_of_exponent_le hw (show (7/8:ℝ)≤1 by norm_num)
  calc
    _ ≤ w^(1/2:ℝ)*(1+Real.log w/Real.log 2)*Real.log w^2 := by
      apply mul_le_mul (pairSieveProperPowers_card U) (pow_le_pow_left₀ hl0 hlw _)
        (sq_nonneg _) (by positivity)
    _ = w^(1/2:ℝ)*Real.log w^2 + (w^(1/2:ℝ)*Real.log w^3)/Real.log 2 := by ring
    _ ≤ (64+512/Real.log 2)*w := by
      calc
        _ ≤ 64*w+512*w/Real.log 2 := add_le_add hterm2 (div_le_div_of_nonneg_right hterm3 htwo.le)
        _ = _ := by ring
    _ ≤ pairSievePowerConstant*U := by
      have hwU : w ≤ 2*(U : ℝ) := by dsimp [w]; exact_mod_cast (show U+1 ≤ 2*U by omega)
      have := mul_le_mul_of_nonneg_left hwU (show 0 ≤ 64+512/Real.log 2 by positivity)
      unfold pairSievePowerConstant
      convert this using 1 <;> ring
end
end HigherCorrelations
