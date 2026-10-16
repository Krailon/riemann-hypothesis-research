import HigherCorrelations.PairSieveBall

/-! UNCONDITIONAL. Every logarithmically nearby pair is covered by a dyadic
ball. Overlaps are permitted because all majorants are nonnegative. -/
namespace HigherCorrelations
noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt

theorem pairSieveBall_mem (δ R : ℝ) (hδ : 0 ≤ δ) (p : ℕ × ℕ)
    (hp : p.1 ≠ p.2 ∧ |Real.log ((p.1+1:ℝ)/(p.2+1:ℝ))| < 2*Real.pi*δ)
    (h1 : (p.1+1:ℝ) ≤ R) (h2 : (p.2+1:ℝ) ≤ R) :
    (p.1+1,p.2+1) ∈ pairSieveNearby R (2*Real.pi*δ*R) := by
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, ?_⟩, mem_Icc.mpr ⟨by omega, ?_⟩⟩,
    ⟨by omega, ?_⟩⟩
  · exact Nat.le_floor (by simpa only [Nat.cast_add, Nat.cast_one] using h1)
  · exact Nat.le_floor (by simpa only [Nat.cast_add, Nat.cast_one] using h2)
  · simpa only [Nat.cast_add, Nat.cast_one] using
      pairSieve_log_band _ _ δ R (by positivity) (by positivity) hδ h1 h2 hp.2

/-- Coefficients of a pair comparable to R have a uniform R^{-3} envelope. -/
theorem pairSieveBall_tail_cover (X δ R : ℝ) (hX : 1 ≤ X) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/2)
    (p : ℕ × ℕ)
    (hp : p.1 ≠ p.2 ∧ |Real.log ((p.1+1:ℝ)/(p.2+1:ℝ))| < 2*Real.pi*δ)
    (hR : 0 < R) (h1 : (p.1+1:ℝ) ≤ R) (h2 : (p.2+1:ℝ) ≤ R)
    (hlo : R ≤ 2*max (p.1+1:ℝ) (p.2+1:ℝ)) :
    pairMeanPrimeCoefficient X p.1*pairMeanPrimeCoefficient X p.2 ≤ pairSieveBall X δ R p := by
  let K := Real.exp Real.pi
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr Real.pi_pos.le
  have hK0 : 0 < K := Real.exp_pos _
  obtain ⟨ha, hb⟩ := pairSieve_log_comparable (p.1+1:ℝ) (p.2+1:ℝ) δ
    (by positivity) (by positivity) hδhi hp.2
  have hm1 : max (p.1+1:ℝ) (p.2+1:ℝ) ≤ K*(p.1+1:ℝ) :=
    max_le (by nlinarith [show (0 : ℝ) ≤ p.1+1 by positivity]) hb
  have hm2 : max (p.1+1:ℝ) (p.2+1:ℝ) ≤ K*(p.2+1:ℝ) :=
    max_le ha (by nlinarith [show (0 : ℝ) ≤ p.2+1 by positivity])
  have hr : 0 < R/(2*K) := by positivity
  have hr1 : R/(2*K) ≤ (p.1+1:ℝ) := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hr2 : R/(2*K) ≤ (p.2+1:ℝ) := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have he := pairSieve_coefficients_tail X (R/(2*K)) hX hr p.1 p.2 hr1 hr2
  unfold pairSieveBall
  rw [ite_eq_left (pairSieveBall_mem δ R hδ p hp h1 h2)]
  convert he using 1 <;> dsimp [K] <;> field_simp <;> ring

/-- The head and every tail pair have at least one valid dyadic covering ball. -/
theorem pairSieveBall_cover (X δ : ℝ) (hX : 1 ≤ X) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/2)
    (p : ℕ × ℕ)
    (hp : p.1 ≠ p.2 ∧ |Real.log ((p.1+1:ℝ)/(p.2+1:ℝ))| < 2*Real.pi*δ) :
    ∃ j : ℕ, pairMeanPrimeCoefficient X p.1*pairMeanPrimeCoefficient X p.2 ≤
      pairSieveBall X δ ((2:ℝ)^j*X) p := by
  have hX0 : 0 < X := by linarith
  let M := max (p.1+1:ℝ) (p.2+1:ℝ)
  by_cases hM : M ≤ X
  · refine ⟨0, ?_⟩
    simp only [pow_zero, one_mul]
    have h1 : (p.1+1:ℝ) ≤ X := (le_max_left _ _).trans hM
    have h2 : (p.2+1:ℝ) ≤ X := (le_max_right _ _).trans hM
    unfold pairSieveBall
    rw [ite_eq_left (pairSieveBall_mem δ X hδ p hp h1 h2)]
    apply (pairSieve_coefficients_head X hX p.1 p.2 h1 h2).trans
    have hK : 1 ≤ Real.exp Real.pi := Real.one_le_exp_iff.mpr Real.pi_pos.le
    have hK3 : 1 ≤ (Real.exp Real.pi)^3 := one_le_pow₀ hK
    have hfactor : 1/X ≤ 8*(Real.exp Real.pi)^3*X^2/X^3 := by
      have he : 8*(Real.exp Real.pi)^3*X^2/X^3 = (8*(Real.exp Real.pi)^3)/X := by field_simp
      rw [he]
      exact div_le_div_of_nonneg_right (by nlinarith) hX0.le
    have hm := mul_le_mul_of_nonneg_right hfactor
      (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := p.1+1))
        (ArithmeticFunction.vonMangoldt_nonneg (n := p.2+1)))
    simpa only [one_div_mul_eq_div] using hm
  · have hMX : 1 ≤ M/X := (one_le_div hX0).mpr (by linarith)
    obtain ⟨j,hjlo,hjhi⟩ := exists_nat_pow_near hMX (show (1 : ℝ)<2 by norm_num)
    refine ⟨j+1, pairSieveBall_tail_cover X δ _ hX hδ hδhi p hp (by positivity) ?_ ?_ ?_⟩
    · exact (le_max_left _ _).trans ((div_lt_iff₀ hX0).mp hjhi).le
    · exact (le_max_right _ _).trans ((div_lt_iff₀ hX0).mp hjhi).le
    · have he := (le_div_iff₀ hX0).mp hjlo
      rw [pow_succ]
      nlinarith
end
end HigherCorrelations
