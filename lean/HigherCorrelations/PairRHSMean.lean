import HigherCorrelations.PairRHSExpansion
import HigherCorrelations.PairRHSCrossTerms
import HigherCorrelations.PairRHSPrimeArch

/-! PAIR-RHS-MEAN-FORMAL-001. UNCONDITIONAL with existential constants.
All actual prime powers and full zero occurrences are retained. -/
namespace HigherCorrelations
noncomputable section

/-- The small error keeps precisely the three terms with the X^{-2} gain. -/
theorem pairRHSSmallError_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T → |pairRHSSmallError X T| ≤ C*(T*Real.log T/X^2) := by
  obtain ⟨K,hK,hk⟩ := pairRHS_remainder_uniform
  refine ⟨64+8*K,by positivity,?_⟩
  intro X T hX hT hXT
  obtain ⟨_,ha,hd,_,_⟩ := hk X T hX hT hXT
  have h1 := pairRHSArchSquareError_bound X T hX hT
  have h2 := pairRHSArchError_small K X T .arch hK.le hX hT ha
  have h3 := pairRHSArchError_small K X T .ds hK.le hX hT hd
  unfold pairRHSSmallError
  calc
    _ ≤ |pairRHSArchSquareError X T|+|pairRHSArchError .arch X T|+
        |pairRHSArchError .ds X T| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (64+8*K)*(T*Real.log T/X^2) := by
      ring_nf at h1 h2 h3 ⊢
      linarith

theorem pairRHSLargeError_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T → |pairRHSLargeError X T| ≤ C*(T*Real.sqrt (Real.log T)) := by
  obtain ⟨C,hC,hc⟩ := pairPrimeMean_uniform
  obtain ⟨K,hK,hk⟩ := pairRHS_remainder_uniform
  refine ⟨3*C+40+16*C*K+8*K+16*K^2,by positivity,?_⟩
  intro X T hX hT hXT
  obtain ⟨hoff,hdiag,hprime⟩ := hc X T hX hT hXT
  obtain ⟨hall,_,_,hp,ht⟩ := hk X T hX hT hXT
  obtain ⟨hsT,hsq,hell,hsprime,hsoff,hsa⟩ := pairRHS_height_scales X T hX hT hXT
  have hT0 : 0 ≤ T := by linarith
  have hX0 : 0 < X := by linarith
  have hq := (pairRHS_log_comparison T hT).1
  have hL : 0 ≤ Real.log (T+2) := Real.log_nonneg (by linarith)
  have hq0 : 0 ≤ Real.log T := by linarith
  have hscale : T ≤ T*Real.sqrt (Real.log T) := by nlinarith
  have hdiag' : |pairPrimeMeanDiagonalError X T| ≤ C*(T*Real.sqrt (Real.log T)) :=
    hdiag.trans (mul_le_mul_of_nonneg_left hscale hC.le)
  have hoff' : |pairPrimeMeanOffdiag X T| ≤ 2*C*(T*Real.sqrt (Real.log T)) := by
    have h := hoff.trans (mul_le_mul_of_nonneg_left hsoff hC.le)
    nlinarith
  have hsX : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0.le).mpr (by nlinarith)
  have hpa : |pairRHSPrimeArchError X T| ≤ 40*(T*Real.sqrt (Real.log T)) := by
    calc
      _ ≤ 20*Real.log (T+2)/Real.sqrt X := pairRHSPrimeArchError_bound X T hX hT0
      _ ≤ 20*Real.log (T+2) := div_le_self (by positivity) hsX
      _ ≤ 40*Real.log T := by linarith [(pairRHS_log_comparison T hT).2.2.2.2]
      _ ≤ _ := by nlinarith [(pairRHS_log_comparison T hT).2.1]
  have hsum : |∑ j, pairRHSPrimeError j X T| ≤ 16*C*K*(T*Real.sqrt (Real.log T)) := by
    calc
      _ ≤ ∑ j, |pairRHSPrimeError j X T| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : PairRemainderKind, 4*C*K*(T*Real.sqrt (Real.log T)) :=
        Finset.sum_le_sum (fun j _ => pairRHSPrimeError_scale C K X T hC.le hK.le hX hT hXT hprime hall j)
      _ = _ := by simp [Finset.univ,Fintype.elems]; ring
  have hAp := pairRHSArchError_large K X T .pole hK.le hX hT hXT hp
  have hAt := pairRHSArchError_large K X T .trivial hK.le hX hT hXT ht
  have hrem : |pairRHSRemainderSquare X T| ≤ 16*K^2*(T*Real.sqrt (Real.log T)) := by
    obtain ⟨hn,hb⟩ := pairRHSRemainderSquare_bound K X T hK.le hX hT0 hall
    rw [abs_of_nonneg hn]
    exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hscale (sq_nonneg K)])
  unfold pairRHSLargeError
  calc
    _ ≤ |pairPrimeMeanDiagonalError X T|+|pairPrimeMeanOffdiag X T|+
        |pairRHSPrimeArchError X T|+|∑ j, pairRHSPrimeError j X T|+
        |pairRHSArchError .pole X T|+|pairRHSArchError .trivial X T|+
        |pairRHSRemainderSquare X T| := by
      apply (abs_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (abs_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (abs_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (abs_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (abs_add_le _ _).trans
      apply add_le_add _ le_rfl
      exact abs_add_le _ _
    _ ≤ (3*C+40+16*C*K+8*K+16*K^2)*(T*Real.sqrt (Real.log T)) := by linarith

/-- Uniform exact decomposition and separately named absolute errors. -/
theorem pairRHSMean_uniform : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    pairRHSSquare X T = pairZeroMeanSquare X T ∧
    pairRHSSquare X T = T*Real.log T^2/X^2+T*Real.log X+
      pairRHSSmallError X T+pairRHSLargeError X T ∧
    |pairRHSSmallError X T| ≤ C₁*(T*Real.log T/X^2) ∧
    |pairRHSLargeError X T| ≤ C₂*(T*Real.sqrt (Real.log T)) := by
  obtain ⟨C₁,hC₁,h₁⟩ := pairRHSSmallError_bound
  obtain ⟨C₂,hC₂,h₂⟩ := pairRHSLargeError_bound
  exact ⟨C₁,hC₁,C₂,hC₂,fun X T hX hT hXT =>
    ⟨pairRHSSquare_eq_zeroMeanSquare X T hX (by linarith),
      pairRHS_decomposition X T hX (by linarith),h₁ X T hX hT hXT,h₂ X T hX hT hXT⟩⟩

/-- The identical norm of the actual zero series has the same absolute error. -/
theorem pairRHSMean_zero_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    |pairZeroMeanSquare X T-(T*Real.log T^2/X^2+T*Real.log X)| ≤
      C*(T*Real.log T/X^2+T*Real.sqrt (Real.log T)) := by
  obtain ⟨A,hA,B,hB,h⟩ := pairRHSMean_uniform
  refine ⟨A+B,by positivity,?_⟩
  intro X T hX hT hXT
  obtain ⟨hz,he,ha,hb⟩ := h X T hX hT hXT
  have hq : 0 ≤ Real.log T := by linarith [(pairRHS_log_comparison T hT).1]
  have ht : 0 ≤ T := by linarith
  have hsmall : 0 ≤ T*Real.log T/X^2 := by positivity
  have hlarge : 0 ≤ T*Real.sqrt (Real.log T) := by positivity
  rw [← hz,he]
  have he' : T*Real.log T^2/X^2+T*Real.log X+pairRHSSmallError X T+pairRHSLargeError X T-
      (T*Real.log T^2/X^2+T*Real.log X) = pairRHSSmallError X T+pairRHSLargeError X T := by ring
  rw [he']
  apply (abs_add_le _ _).trans
  have h1 := mul_nonneg hA.le hlarge
  have h2 := mul_nonneg hB.le hsmall
  nlinarith

theorem pairRHSMean_unit : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
    |pairZeroMeanSquare 1 T-T*Real.log T^2| ≤ C*(T*Real.log T+T*Real.sqrt (Real.log T)) := by
  obtain ⟨C,hC,h⟩ := pairRHSMean_zero_bound
  exact ⟨C,hC,fun T hT => by simpa using h 1 T (by norm_num) hT (by linarith)⟩

theorem pairRHSMean_top : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
    |pairZeroMeanSquare T T-(T*Real.log T^2/T^2+T*Real.log T)| ≤
      C*(T*Real.log T/T^2+T*Real.sqrt (Real.log T)) := by
  obtain ⟨C,hC,h⟩ := pairRHSMean_zero_bound
  exact ⟨C,hC,fun T hT => h T T (by linarith) hT le_rfl⟩

theorem pairRHSMean_minimal_height : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → X ≤ 3 →
    |pairZeroMeanSquare X 3-(3*Real.log 3^2/X^2+3*Real.log X)| ≤
      C*(3*Real.log 3/X^2+3*Real.sqrt (Real.log 3)) := by
  obtain ⟨C,hC,h⟩ := pairRHSMean_zero_bound
  exact ⟨C,hC,fun X hX hXT => h X 3 hX (by norm_num) hXT⟩

end
end HigherCorrelations
