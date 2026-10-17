import HigherCorrelations.PairPrimeMeanEstimate

/-! UNCONDITIONAL. Assembled prime mean-square bounds with named errors.
Constants are existential; no relative asymptotic is asserted at X=1. -/
namespace HigherCorrelations
noncomputable section

theorem pairPrimeMean_combined_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    |pairPrimeMeanSquare X T-T*Real.log X| ≤ C*(T+Real.sqrt (T*X*Real.log (2*X))) := by
  obtain ⟨A,hA,ha⟩ := pairPrimeMeanOffdiag_bound
  obtain ⟨B,hB,hb⟩ := pairPrimeMeanDiagonalError_bound
  refine ⟨A+B, by positivity, ?_⟩
  intro X T hX hT hXT
  have he : pairPrimeMeanSquare X T-T*Real.log X =
      pairPrimeMeanDiagonalError X T+pairPrimeMeanOffdiag X T := by
    unfold pairPrimeMeanDiagonalError pairPrimeMeanOffdiag; ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hs := Real.sqrt_nonneg (T*X*Real.log (2*X))
  have ht : 0 ≤ T := by linarith
  nlinarith [ha X T hX hT hXT,hb X T hX ht]

/-- One constant works for every parameter in the closed range. -/
theorem pairPrimeMean_uniform : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    |pairPrimeMeanOffdiag X T| ≤ C*Real.sqrt (T*X*Real.log (2*X)) ∧
    |pairPrimeMeanDiagonalError X T| ≤ C*T ∧
    pairPrimeMeanL2Norm X T ≤ C*Real.sqrt (T*Real.log (2*X)) := by
  obtain ⟨A,hA,ha⟩ := pairPrimeMeanOffdiag_bound
  obtain ⟨B,hB,hb⟩ := pairPrimeMeanDiagonalError_bound
  obtain ⟨D,hD,hd⟩ := pairPrimeMeanL2Norm_bound
  refine ⟨A+B+D, by positivity, ?_⟩
  intro X T hX hT hXT
  refine ⟨(ha X T hX hT hXT).trans ?_, (hb X T hX (by linarith)).trans ?_,
    (hd X T hX hT hXT).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  · exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

theorem pairPrimeMean_unit : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
    |pairPrimeMeanOffdiag 1 T| ≤ C*Real.sqrt (T*Real.log 2) ∧
    |pairPrimeMeanDiagonalError 1 T| ≤ C*T := by
  obtain ⟨C,hC,hb⟩ := pairPrimeMean_uniform
  refine ⟨C,hC,?_⟩
  intro T hT
  have h := hb 1 T le_rfl hT (by linarith)
  have hp := And.intro h.1 h.2.1
  simpa only [mul_one] using hp

theorem pairPrimeMean_top : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
    |pairPrimeMeanOffdiag T T| ≤ C*Real.sqrt (T*T*Real.log (2*T)) ∧
    |pairPrimeMeanDiagonalError T T| ≤ C*T := by
  obtain ⟨C,hC,hb⟩ := pairPrimeMean_uniform
  refine ⟨C,hC,?_⟩
  intro T hT
  have h := hb T T (by linarith) hT le_rfl
  exact ⟨h.1,h.2.1⟩

theorem pairPrimeMean_minimal_height : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → X ≤ 3 →
    |pairPrimeMeanOffdiag X 3| ≤ C*Real.sqrt (3*X*Real.log (2*X)) ∧
    |pairPrimeMeanDiagonalError X 3| ≤ C*3 := by
  obtain ⟨C,hC,hb⟩ := pairPrimeMean_uniform
  refine ⟨C,hC,?_⟩
  intro X hX hhi
  have h := hb X 3 hX le_rfl hhi
  exact ⟨h.1,h.2.1⟩

end
end HigherCorrelations
