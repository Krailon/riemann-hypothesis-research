import HigherCorrelations.TripleProperPowerCount
import HigherCorrelations.TripleResonanceMajorant
import HigherCorrelations.PairDiagonalPowerBound

/-! UNCONDITIONAL finite dyadic ball cover. Every integer upper cutoff is
inclusive, and all overlapping cover contributions are nonnegative. -/
namespace HigherCorrelations
noncomputable section
open Finset

theorem tripleResonanceBall_nonneg (Z R : ℝ) (hR : 1 ≤ R) (n : ℕ) :
    0 ≤ tripleResonanceBall Z R n := by
  have hl : 0 ≤ Real.log (2*R) := Real.log_nonneg (by linarith)
  unfold tripleResonanceBall
  split_ifs <;> positivity

theorem tripleResonanceBall_support (Z R : ℝ) (n : ℕ)
    (hn : n ∉ Icc 0 ⌊R⌋₊) : tripleResonanceBall Z R n = 0 := by
  unfold tripleResonanceBall
  apply ite_eq_right
  intro h
  exact hn (mem_Icc.mpr ⟨Nat.zero_le _,h.1⟩)

theorem tripleResonanceBall_summable (Z R : ℝ) : Summable (tripleResonanceBall Z R) :=
  summable_of_ne_finset_zero (tripleResonanceBall_support Z R)

theorem tripleResonanceBall_sum (Z R : ℝ) :
    (∑' n, tripleResonanceBall Z R n) =
      (8*Z^2/R^3)*Real.log (2*R)^3*((pairSieveProperPowers ⌊R⌋₊).card:ℝ) := by
  rw [tsum_eq_sum (tripleResonanceBall_support Z R)]
  have hs : (Icc 0 ⌊R⌋₊).filter (fun n => IsPrimePow n ∧ ¬n.Prime) =
      pairSieveProperPowers ⌊R⌋₊ := by
    ext n
    simp only [pairSieveProperPowers,mem_filter,mem_Icc]
    constructor
    · rintro ⟨⟨_,hn⟩,hpp⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hpp.1.ne_zero,hn⟩,hpp⟩
    · rintro ⟨⟨_,hn⟩,hpp⟩; exact ⟨⟨Nat.zero_le _,hn⟩,hpp⟩
  simp only [tripleResonanceBall,show ∀ n ∈ Icc 0 ⌊R⌋₊, n ≤ ⌊R⌋₊ from fun _ hn => (mem_Icc.mp hn).2]
  have he : (∑ n ∈ Icc 0 ⌊R⌋₊, if n ≤ ⌊R⌋₊ ∧ IsPrimePow n ∧ ¬n.Prime then
      (8*Z^2/R^3)*Real.log (2*R)^3 else 0) =
      ∑ n ∈ Icc 0 ⌊R⌋₊, if IsPrimePow n ∧ ¬n.Prime then (8*Z^2/R^3)*Real.log (2*R)^3 else 0 := by
    apply sum_congr rfl; intro n hn
    simp only [(mem_Icc.mp hn).2,true_and]
  rw [he,← sum_filter,hs,sum_const,nsmul_eq_mul]
  ring

theorem tripleResonanceBall_dyadic_bound (Z : ℝ) (hZ : 1 ≤ Z) (j : ℕ) :
    (∑' n, tripleResonanceBall Z ((2:ℝ)^j*Z) n) ≤
      (8*tripleProperPowerConstant*tripleResonanceScale Z)*((j+1:ℝ)^3*(1/4:ℝ)^j) := by
  have hZ0 : 0 < Z := by linarith
  have hp : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hp0 : 0 < (2:ℝ)^j := by positivity
  have hR : 1 ≤ (2:ℝ)^j*Z := one_le_mul_of_one_le_of_one_le hp hZ
  have hl : 0 ≤ Real.log (2*Z) := Real.log_nonneg (by linarith)
  have hs : Real.sqrt ((2:ℝ)^j*Z) ≤ (2:ℝ)^j*Real.sqrt Z := by
    rw [Real.sqrt_mul hp0.le]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_left hp0.le).mpr (by nlinarith)
  have hlog : Real.log (2*((2:ℝ)^j*Z)) ≤ (j+1:ℝ)*Real.log (2*Z) := by
    rw [show 2*((2:ℝ)^j*Z) = (2:ℝ)^j*(2*Z) by ring,
      Real.log_mul hp0.ne' (by positivity),Real.log_pow]
    have hlow : Real.log 2 ≤ Real.log (2*Z) := Real.log_le_log (by norm_num) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg (α := ℝ) j)]
  have hlog0 : 0 ≤ Real.log (2*((2:ℝ)^j*Z)) := Real.log_nonneg (by nlinarith)
  have hc := (tripleProperPower_count _ hR).trans
    (mul_le_mul_of_nonneg_left hs tripleProperPowerConstant_pos.le)
  rw [tripleResonanceBall_sum]
  apply (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 3)
    (by positivity : 0 ≤ 8*Z^2/((2:ℝ)^j*Z)^3)) hc (Nat.cast_nonneg _) (by positivity)).trans
  apply le_of_eq
  unfold tripleResonanceScale
  have hsZ : (Real.sqrt Z)^2 = Z := Real.sq_sqrt hZ0.le
  have hs0 : Real.sqrt Z ≠ 0 := (Real.sqrt_pos.mpr hZ0).ne'
  have he : (1/4:ℝ)^j = 1/((2:ℝ)^j)^2 := by
    rw [one_div_pow,← pow_mul,mul_comm j 2,pow_mul]
    norm_num
  rw [he]
  field_simp
  rw [hsZ]
  ring

theorem tripleResonanceBall_cover (Z : ℝ) (hZ : 1 ≤ Z) (n : ℕ)
    (hn : IsPrimePow n ∧ ¬n.Prime) : ∃ j : ℕ,
    tripleResonanceMajorant Z n ≤ tripleResonanceBall Z ((2:ℝ)^j*Z) n := by
  have hZ0 : 0 < Z := by linarith
  have hnN : 0 < n := Nat.pos_of_ne_zero hn.1.ne_zero
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnN
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hid : tripleResonanceMajorant Z n = pairDiagonalWeight Z n*Real.log n^3 := by
    rw [tripleResonanceMajorant,if_pos hn,← tripleResonance_weight_identity Z hZ n hnN]
    ring
  rw [hid]
  by_cases h : (n:ℝ) ≤ Z
  · refine ⟨0,?_⟩
    have hl : Real.log n ≤ Real.log (2*Z) := Real.log_le_log hn0 (by linarith)
    simp only [pow_zero,one_mul,tripleResonanceBall,Nat.le_floor h,hn,true_and,ite_true,
      pairDiagonalWeight,h]
    have hc : (n:ℝ)/Z^2 ≤ 8*Z^2/Z^3 := by
      apply (div_le_div_of_nonneg_right h (sq_nonneg Z)).trans
      field_simp
      nlinarith
    exact mul_le_mul hc (pow_le_pow_left₀ hln hl 3) (by positivity) (by positivity)
  · obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near
      ((one_le_div hZ0).mpr (by linarith : Z ≤ (n:ℝ))) (show (1:ℝ)<2 by norm_num)
    have hR : (n:ℝ) ≤ (2:ℝ)^(j+1)*Z := ((div_lt_iff₀ hZ0).mp hhi).le
    have hRlo : (2:ℝ)^(j+1)*Z ≤ 2*(n:ℝ) := by
      have := (le_div_iff₀ hZ0).mp hlo
      rw [pow_succ]; nlinarith
    refine ⟨j+1,?_⟩
    have hl : Real.log n ≤ Real.log (2*((2:ℝ)^(j+1)*Z)) := Real.log_le_log hn0 (by linarith)
    simp only [tripleResonanceBall,Nat.le_floor hR,hn,true_and,ite_true,pairDiagonalWeight,h,ite_false]
    have hc : Z^2/(n:ℝ)^3 ≤ 8*Z^2/((2:ℝ)^(j+1)*Z)^3 := by
      have hc := pow_le_pow_left₀ (by positivity : 0 ≤ (2:ℝ)^(j+1)*Z) hRlo 3
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg Z)]
    exact mul_le_mul hc (pow_le_pow_left₀ hln hl 3) (by positivity) (by positivity)

end
end HigherCorrelations
