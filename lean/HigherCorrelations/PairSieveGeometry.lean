import HigherCorrelations.PairMeanPrimeBridge

/-! UNCONDITIONAL. The strict logarithmic band implies a closed linear band,
and the actual coefficients have uniform head and tail envelopes. -/
namespace HigherCorrelations
noncomputable section

theorem pairSieve_log_distance (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    |a-b| ≤ max a b * |Real.log (a/b)| := by
  have haux (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
      x-y ≤ x*Real.log (x/y) := by
    have he := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos (div_pos hx hy)) hx.le
    have hid : x*(1-(x/y)⁻¹) = x-y := by field_simp
    rwa [hid] at he
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left h]
    exact (haux a b ha hb).trans (mul_le_mul_of_nonneg_left (le_abs_self _) ha.le)
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right h]
    have he := (haux b a hb ha).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hb.le)
    have hl : |Real.log (b/a)| = |Real.log (a/b)| := by
      rw [Real.log_div hb.ne' ha.ne', Real.log_div ha.ne' hb.ne', abs_sub_comm]
    rw [hl] at he
    linarith

theorem pairSieve_log_comparable (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : δ ≤ 1/2) (hband : |Real.log (a/b)| < 2*Real.pi*δ) :
    a ≤ Real.exp Real.pi*b ∧ b ≤ Real.exp Real.pi*a := by
  have hp := Real.pi_pos
  have hl : |Real.log (a/b)| ≤ Real.pi := by nlinarith
  have hupper : a/b ≤ Real.exp Real.pi := by
    rw [← Real.exp_log (div_pos ha hb)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hl)
  have hl' : Real.log (b/a) = -Real.log (a/b) := by
    rw [Real.log_div hb.ne' ha.ne', Real.log_div ha.ne' hb.ne']; ring
  have hupper' : b/a ≤ Real.exp Real.pi := by
    rw [← Real.exp_log (div_pos hb ha)]
    apply Real.exp_le_exp.mpr
    rw [hl']
    exact (neg_le_abs _).trans hl
  exact ⟨(div_le_iff₀ hb).mp hupper, (div_le_iff₀ ha).mp hupper'⟩

theorem pairSieve_log_band (a b δ R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (haR : a ≤ R) (hbR : b ≤ R)
    (hband : |Real.log (a/b)| < 2*Real.pi*δ) : |a-b| ≤ 2*Real.pi*δ*R := by
  calc
    _ ≤ max a b*|Real.log (a/b)| := pairSieve_log_distance a b ha hb
    _ ≤ R*(2*Real.pi*δ) := mul_le_mul (max_le haR hbR) hband.le
      (abs_nonneg _) (ha.le.trans haR)
    _ = _ := by ring

/-- The growing envelope is valid even beyond its eventual cutoff. -/
theorem pairSieve_coefficient_head (X R : ℝ) (hX : 0 < X) (n : ℕ)
    (hnR : (n+1:ℝ) ≤ R) :
    pairMeanPrimeCoefficient X n ≤ ArithmeticFunction.vonMangoldt (n+1)*Real.sqrt R/X := by
  have hn : 0 < (n+1:ℝ) := by positivity
  have hs : 0 < Real.sqrt (n+1:ℝ) := Real.sqrt_pos.mpr hn
  rw [pairMeanPrimeCoefficient_sqrt]
  calc
    _ ≤ ArithmeticFunction.vonMangoldt (n+1)/Real.sqrt (n+1:ℝ)*((n+1:ℝ)/X) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le)
    _ = ArithmeticFunction.vonMangoldt (n+1)*Real.sqrt (n+1:ℝ)/X := by
      have he := Real.sq_sqrt hn.le
      field_simp
      rw [he]
    _ ≤ _ := by gcongr

/-- The decreasing envelope is valid below as well as above X. -/
theorem pairSieve_coefficient_tail (X r : ℝ) (hX : 0 < X) (hr : 0 < r)
    (n : ℕ) (hrn : r ≤ (n+1:ℝ)) :
    pairMeanPrimeCoefficient X n ≤ ArithmeticFunction.vonMangoldt (n+1)*X/(r*Real.sqrt r) := by
  have hn : 0 < (n+1:ℝ) := by positivity
  have hs : 0 < Real.sqrt (n+1:ℝ) := Real.sqrt_pos.mpr hn
  rw [pairMeanPrimeCoefficient_sqrt]
  calc
    _ ≤ ArithmeticFunction.vonMangoldt (n+1)/Real.sqrt (n+1:ℝ)*(X/(n+1:ℝ)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le)
    _ = ArithmeticFunction.vonMangoldt (n+1)*X/((n+1:ℝ)*Real.sqrt (n+1:ℝ))  := by field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr

theorem pairSieve_coefficients_head (X : ℝ) (hX : 1 ≤ X) (m n : ℕ)
    (hm : (m+1:ℝ) ≤ X) (hn : (n+1:ℝ) ≤ X) :
    pairMeanPrimeCoefficient X m*pairMeanPrimeCoefficient X n ≤
      ArithmeticFunction.vonMangoldt (m+1)*ArithmeticFunction.vonMangoldt (n+1)/X := by
  have hX0 : 0 < X := by linarith
  have he := mul_le_mul (pairSieve_coefficient_head X X hX0 m hm)
    (pairSieve_coefficient_head X X hX0 n hn)
    (pairMeanPrimeCoefficient_nonneg X hX n) (by positivity)
  have hid : (ArithmeticFunction.vonMangoldt (m+1)*Real.sqrt X/X)*
      (ArithmeticFunction.vonMangoldt (n+1)*Real.sqrt X/X) =
      ArithmeticFunction.vonMangoldt (m+1)*ArithmeticFunction.vonMangoldt (n+1)/X := by
    have hs := Real.sq_sqrt hX0.le
    field_simp
    rw [hs]
  rwa [hid] at he

theorem pairSieve_coefficients_tail (X r : ℝ) (hX : 1 ≤ X) (hr : 0 < r) (m n : ℕ)
    (hm : r ≤ (m+1:ℝ)) (hn : r ≤ (n+1:ℝ)) :
    pairMeanPrimeCoefficient X m*pairMeanPrimeCoefficient X n ≤
      (X^2/r^3)*(ArithmeticFunction.vonMangoldt (m+1)*ArithmeticFunction.vonMangoldt (n+1)) := by
  have hX0 : 0 < X := by linarith
  have he := mul_le_mul (pairSieve_coefficient_tail X r hX0 hr m hm)
    (pairSieve_coefficient_tail X r hX0 hr n hn)
    (pairMeanPrimeCoefficient_nonneg X hX n) (by positivity)
  have hid : (ArithmeticFunction.vonMangoldt (m+1)*X/(r*Real.sqrt r))*
      (ArithmeticFunction.vonMangoldt (n+1)*X/(r*Real.sqrt r)) =
      (X^2/r^3)*(ArithmeticFunction.vonMangoldt (m+1)*ArithmeticFunction.vonMangoldt (n+1)) := by
    have hs := Real.sq_sqrt hr.le
    have hs0 := Real.sqrt_pos.mpr hr
    field_simp
    rw [hs]
  rwa [hid] at he
end
end HigherCorrelations
