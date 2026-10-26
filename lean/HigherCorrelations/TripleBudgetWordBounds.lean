import HigherCorrelations.TripleBudgetSlots
import HigherCorrelations.TripleBudgetRefinement
import HigherCorrelations.TripleBudgetRemainders

/-! UNCONDITIONAL bounds for each ordered remainder assignment and each word. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudgetLetterNorm_nonneg (ω : ℝ → ℝ) (T x : ℝ) (hT : 3≤T) (hx : 1≤x) (l : MasterLetter) :
    0≤tripleBudgetLetterNorm ω T x l := by
  cases l
  · exact Real.sqrt_nonneg _
  · exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  · change 0≤∑ j, tripleBudgetRemainderBound j T x
    exact Finset.sum_nonneg (fun j _ => tripleBudgetRemainderBound_nonneg j T x hT hx)

theorem tripleBudget_component_L2 (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T x : ℝ) (hT : 3≤T) (hx : 1≤x) (l : MasterLetter) :
    tripleBudgetL2 ω T (tripleComponent l x) ≤ tripleBudgetLetterNorm ω T x l := by
  cases l
  · exact le_rfl
  · exact tripleBudgetL2_sup ω hω T (by linarith) _ (tripleComponent_continuous _ x hx) _
      (tripleBudgetLetterNorm_nonneg ω T x hT hx .A) (fun t ht => tripleBudget_arch_bound T x t hT hx ht)
  · exact tripleBudgetL2_sup ω hω T (by linarith) _ (tripleComponent_continuous _ x hx) _
      (tripleBudgetLetterNorm_nonneg ω T x hT hx .H) (fun t ht => tripleBudget_remainder_total_bound T x t hT hx ht)

theorem tripleBudgetRefinedNorm_nonneg (ω : ℝ → ℝ) (T x : ℝ) (hT : 3≤T) (hx : 1≤x)
    (w : MasterWord) (κ : TripleBudgetAssignment w) (r : Fin 3) :
    0≤tripleBudgetRefinedNorm ω T x w κ r := by
  unfold tripleBudgetRefinedNorm
  split_ifs
  · exact tripleBudgetRemainderBound_nonneg _ T x hT hx
  · exact tripleBudgetLetterNorm_nonneg ω T x hT hx _

theorem tripleBudget_refined_L2 (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T x : ℝ) (hT : 3≤T) (hx : 1≤x) (w : MasterWord) (κ : TripleBudgetAssignment w) (r : Fin 3) :
    tripleBudgetL2 ω T (tripleBudgetRefinedComponent w κ r x) ≤ tripleBudgetRefinedNorm ω T x w κ r := by
  unfold tripleBudgetRefinedComponent tripleBudgetRefinedNorm
  split_ifs
  · exact tripleBudgetL2_sup ω hω T (by linarith) _ (pairRHS_remainder_continuous _ x hx) _
      (tripleBudgetRemainderBound_nonneg _ T x hT hx) (fun t ht => tripleBudget_remainder_bound _ T x t hT hx ht)
  · exact tripleBudget_component_L2 ω hω T x hT hx _

theorem tripleWordSign_norm (w : MasterWord) : ‖(tripleWordSign w:ℂ)‖=1 := by
  simp [tripleWordSign,norm_pow]

theorem tripleBudget_refined_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (w : MasterWord)
    (hw : tripleWordHasH w = true) (κ : TripleBudgetAssignment w) :
    ‖tripleBudgetRefinedError ω T X Y w κ‖ ≤
      ∏ r : Fin 3, tripleBudgetRefinedNorm ω T (![X,Y,X*Y] r) w κ r := by
  have hZ : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hx (r : Fin 3) : 1≤(![X,Y,X*Y] r) := by fin_cases r <;> assumption
  obtain ⟨r,hr⟩ := of_decide_eq_true hw
  have hb := tripleBudget_slots_bound ω hω T (by linarith)
    (fun i => tripleBudgetRefinedComponent w κ i (![X,Y,X*Y] i))
    (fun i => tripleBudgetRefinedComponent_continuous w κ i _ (hx i))
    (fun i => tripleBudgetRefinedNorm ω T (![X,Y,X*Y] i) w κ i)
    (fun i => tripleBudgetRefinedNorm_nonneg ω T _ hT (hx i) w κ i)
    (fun i => tripleBudget_refined_L2 ω hω T _ hT (hx i) w κ i) r (by
      intro t ht
      simp only [tripleBudgetRefinedComponent,tripleBudgetRefinedNorm,dif_pos hr]
      exact tripleBudget_remainder_bound _ T _ t hT (hx r) ht)
  rw [tripleBudgetRefinedError,norm_mul,tripleWordSign_norm,one_mul]
  simpa [
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] using hb

theorem tripleBudget_word_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (w : MasterWord)
    (hw : tripleWordHasH w = true) :
    ‖tripleBudgetWordError ω T X Y w‖ ≤ ∏ r : Fin 3, tripleBudgetLetterNorm ω T (![X,Y,X*Y] r) (w r) := by
  have hZ : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hx (r : Fin 3) : 1≤(![X,Y,X*Y] r) := by fin_cases r <;> assumption
  obtain ⟨r,hr⟩ := of_decide_eq_true hw
  have hb := tripleBudget_slots_bound ω hω T (by linarith)
    (fun i => tripleComponent (w i) (![X,Y,X*Y] i))
    (fun i => tripleComponent_continuous _ _ (hx i))
    (fun i => tripleBudgetLetterNorm ω T (![X,Y,X*Y] i) (w i))
    (fun i => tripleBudgetLetterNorm_nonneg ω T _ hT (hx i) _)
    (fun i => tripleBudget_component_L2 ω hω T _ hT (hx i) _) r (by
      intro t ht
      rw [hr]
      exact tripleBudget_remainder_total_bound T _ t hT (hx r) ht)
  rw [tripleBudgetWordError,norm_mul,tripleWordSign_norm,one_mul]
  simpa [tripleWordIntegral,tripleWordIntegrand,tripleSmoothedIntegral,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] using hb

end
end HigherCorrelations
