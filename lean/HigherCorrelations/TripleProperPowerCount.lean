import HigherCorrelations.TripleResonanceDecayDefinitions
import HigherCorrelations.PairSievePrimePowers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! UNCONDITIONAL square-root count with no logarithmic loss. Squares are
separated from higher powers. The cover counts bases, not just primes. -/
namespace HigherCorrelations
noncomputable section
open Finset

theorem tripleProperPowerConstant_pos : 0 < tripleProperPowerConstant := by
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold tripleProperPowerConstant
  positivity

theorem tripleProperPower_exponent_bound (u : ℝ) (p k : ℕ)
    (hp : p.Prime) (hpu : (p:ℝ)^k ≤ u) : (k:ℝ) ≤ Real.log u/Real.log 2 := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hl := Real.log_le_log (pow_pos hp0 k) hpu
  rw [Real.log_pow] at hl
  have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hp2
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  exact (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)).trans hl

theorem tripleProperPower_cover (u : ℝ) (hu : 1 ≤ u) :
    pairSieveProperPowers ⌊u⌋₊ ⊆
      ((Icc 1 ⌊Real.sqrt u⌋₊).image (fun p : ℕ => p^2)) ∪
      (((Icc 1 ⌊u^(1/3:ℝ)⌋₊) ×ˢ (Icc 1 ⌊Real.log u/Real.log 2⌋₊)).image
        (fun q : ℕ × ℕ => q.1^q.2)) := by
  intro n hn
  obtain ⟨hni,hnpp,hnp⟩ := mem_filter.mp hn
  have hnu : (n:ℝ) ≤ u := (Nat.le_floor_iff (by linarith : 0 ≤ u)).mp (mem_Icc.mp hni).2
  obtain ⟨p,k,hp,hk,hpk⟩ := (isPrimePow_nat_iff n).mp hnpp
  have hk2 : 2 ≤ k := by
    by_contra h
    have he : k=1 := by omega
    simp only [he,pow_one] at hpk
    exact hnp (hpk ▸ hp)
  have hpu : (p:ℝ)^k ≤ u := by exact_mod_cast (hpk ▸ hnu : ((p^k:ℕ):ℝ) ≤ u)
  by_cases he : k=2
  · apply mem_union_left
    apply mem_image.mpr
    refine ⟨p,mem_Icc.mpr ⟨hp.one_le,?_⟩,?_⟩
    · apply Nat.le_floor
      apply (Real.le_sqrt (Nat.cast_nonneg _) (by linarith : 0 ≤ u)).mpr
      simpa only [he] using hpu
    · simpa only [he] using hpk
  · apply mem_union_right
    apply mem_image.mpr
    refine ⟨(p,k),mem_product.mpr ⟨mem_Icc.mpr ⟨hp.one_le,?_⟩,
      mem_Icc.mpr ⟨by omega,?_⟩⟩,hpk⟩
    · apply Nat.le_floor
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
      have hp3 : (p:ℝ)^3 ≤ u := (pow_le_pow_right₀ hp1 (by omega : 3 ≤ k)).trans hpu
      have hroot := (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p)
        (by linarith : 0 ≤ u) (by norm_num : (0:ℝ)<3)).mpr
        (by simpa only [show (3:ℝ)=(3:ℕ) by norm_num,Real.rpow_natCast] using hp3)
      simpa only [one_div] using hroot
    · exact Nat.le_floor (tripleProperPower_exponent_bound u p k hp hpu)

/-- Inclusive real cutoffs; the overcounted images may overlap harmlessly. -/
theorem tripleProperPower_count_raw (u : ℝ) (hu : 1 ≤ u) :
    ((pairSieveProperPowers ⌊u⌋₊).card:ℝ) ≤
      Real.sqrt u+u^(1/3:ℝ)*(Real.log u/Real.log 2) := by
  have hc := card_le_card (tripleProperPower_cover u hu)
  have hb := hc.trans ((card_union_le _ _).trans (Nat.add_le_add (card_image_le) (card_image_le)))
  simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel] at hb
  have hbr : ((pairSieveProperPowers ⌊u⌋₊).card:ℝ) ≤
      (⌊Real.sqrt u⌋₊:ℝ)+(⌊u^(1/3:ℝ)⌋₊:ℝ)*(⌊Real.log u/Real.log 2⌋₊:ℝ) := by exact_mod_cast hb
  apply hbr.trans
  apply add_le_add (Nat.floor_le (Real.sqrt_nonneg _))
  exact mul_le_mul (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
    (Nat.floor_le (div_nonneg (Real.log_nonneg hu) (Real.log_pos (by norm_num)).le))
    (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)

theorem tripleProperPower_count (u : ℝ) (hu : 1 ≤ u) :
    ((pairSieveProperPowers ⌊u⌋₊).card:ℝ) ≤ tripleProperPowerConstant*Real.sqrt u := by
  have hu0 : 0 < u := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log u ≤ 6*u^(1/6:ℝ) := by
    have h := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ)<1/6)
    linarith
  have hp : u^(1/3:ℝ)*u^(1/6:ℝ) = Real.sqrt u := by
    rw [← Real.rpow_add hu0]
    norm_num
    rw [Real.sqrt_eq_rpow]
  calc
    _ ≤ Real.sqrt u+u^(1/3:ℝ)*(Real.log u/Real.log 2) := tripleProperPower_count_raw u hu
    _ ≤ Real.sqrt u+u^(1/3:ℝ)*(6*u^(1/6:ℝ)/Real.log 2) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hl hl2.le) (Real.rpow_nonneg hu0.le _))
    _ = _ := by unfold tripleProperPowerConstant; rw [show u^(1/3:ℝ)*(6*u^(1/6:ℝ)/Real.log 2) = (6/Real.log 2)*(u^(1/3:ℝ)*u^(1/6:ℝ)) by ring,hp]; ring

theorem tripleProperPower_count_one : pairSieveProperPowers 1 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨⟨hn1,hn2⟩,hn,_⟩ := (by simpa only [pairSieveProperPowers,mem_filter,mem_Icc] using hn)
  have he : n=1 := by omega
  exact hn.ne_one he

end
end HigherCorrelations
