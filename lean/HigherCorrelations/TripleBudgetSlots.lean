import HigherCorrelations.TripleBudgetL2

/-! UNCONDITIONAL slotwise bounds, retaining the third-slot conjugation. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudget_integral_first_sup (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (f g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h)
    (B : ℝ) (hB : 0≤B) (hb : ∀ t ∈ Icc T (2*T), ‖f t‖≤B) :
    ‖tripleSmoothedIntegral ω T f g h‖ ≤ tripleBudgetL2 ω T g*tripleBudgetL2 ω T h*B := by
  have hw (t : ℝ) : 0≤ω (t/T)/T := div_nonneg (hω.nonneg _) hT.le
  have hp (t : ℝ) : ‖tripleSmoothedIntegrand ω T f g h t‖ ≤ (ω (t/T)/T*‖g t‖*‖h t‖)*B := by
    simp only [tripleSmoothedIntegrand,norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw t)]
    by_cases hz : ω (t/T)=0
    · simp [hz]
    · have hs := hb t (tripleMaster_support ω (tripleBudgetWeight_support ω hω) T hT hz)
      nlinarith [mul_nonneg (hw t) (mul_nonneg (norm_nonneg (g t)) (norm_nonneg (h t)))]
  have hi : Integrable (fun t => (ω (t/T)/T*‖g t‖*‖h t‖)*B) := by
    simpa only [Pi.mul_apply,mul_assoc] using (tripleBudget_weighted_integrable ω hω T hT _ (hg.norm.mul hh.norm)).mul_const B
  calc
    _ ≤ ∫ t : ℝ, (ω (t/T)/T*‖g t‖*‖h t‖)*B := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hp)
    _ = (∫ t : ℝ, ω (t/T)/T*‖g t‖*‖h t‖)*B := integral_mul_const B _
    _ ≤ _ := mul_le_mul_of_nonneg_right (tripleBudgetL2_cauchy ω hω T hT g h hg hh) hB

theorem tripleBudget_integral_second_sup (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (f g h : ℝ → ℂ) (hf : Continuous f) (hh : Continuous h)
    (B : ℝ) (hB : 0≤B) (hb : ∀ t ∈ Icc T (2*T), ‖g t‖≤B) :
    ‖tripleSmoothedIntegral ω T f g h‖ ≤ tripleBudgetL2 ω T f*tripleBudgetL2 ω T h*B := by
  have he : tripleSmoothedIntegral ω T f g h = tripleSmoothedIntegral ω T g f h := by
    unfold tripleSmoothedIntegral tripleSmoothedIntegrand
    congr 1
    funext t
    ring
  rw [he]
  exact tripleBudget_integral_first_sup ω hω T hT g f h hf hh B hB hb

theorem tripleBudget_slots_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (f : Fin 3 → ℝ → ℂ) (hf : ∀ r, Continuous (f r))
    (B : Fin 3 → ℝ) (hB : ∀ r, 0≤B r) (hL : ∀ r, tripleBudgetL2 ω T (f r)≤B r)
    (r : Fin 3) (hs : ∀ t ∈ Icc T (2*T), ‖f r t‖≤B r) :
    ‖tripleSmoothedIntegral ω T (f 0) (f 1) (f 2)‖ ≤ ∏ r : Fin 3, B r := by
  have hL0 (r : Fin 3) : 0≤tripleBudgetL2 ω T (f r) := Real.sqrt_nonneg _
  rw [Fin.prod_univ_three]
  fin_cases r
  · apply (tripleBudget_integral_first_sup ω hω T hT _ _ _ (hf 1) (hf 2) _ (hB 0) hs).trans
    calc
      _ ≤ B 1*B 2*B 0 := mul_le_mul_of_nonneg_right (mul_le_mul (hL 1) (hL 2) (hL0 2) (hB 1)) (hB 0)
      _ = _ := by ring
  · apply (tripleBudget_integral_second_sup ω hω T hT _ _ _ (hf 0) (hf 2) _ (hB 1) hs).trans
    calc
      _ ≤ B 0*B 2*B 1 := mul_le_mul_of_nonneg_right (mul_le_mul (hL 0) (hL 2) (hL0 2) (hB 0)) (hB 1)
      _ = _ := by ring
  · exact (tripleBudget_integral_norm_bound ω hω T hT _ _ _ (hf 0) (hf 1) _ (hB 2) hs).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul (hL 0) (hL 1) (hL0 1) (hB 0)) (hB 2))

end
end HigherCorrelations
