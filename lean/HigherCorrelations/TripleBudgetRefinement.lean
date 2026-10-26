import HigherCorrelations.TripleBudgetAccounting

/-! UNCONDITIONAL finite refinement of the nineteen remainder words.
The 208 refined terms are an alternative description, never extra errors. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudget_refinement_algebra {R : Type*} [CommSemiring R] (w : MasterWord)
    (F : Fin 3 → PairRemainderKind → R) (G : Fin 3 → R) :
    (∏ r : Fin 3, if w r = .H then ∑ j, F r j else G r) =
      ∑ κ : TripleBudgetAssignment w, ∏ r : Fin 3,
        if h : w r = .H then F r (κ ⟨r,h⟩) else G r := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun r => w r = .H)]
  have hp (r : {r : Fin 3 // w r = .H}) :
      (if w r.val = .H then ∑ j, F r.val j else G r.val) = ∑ j, F r.val j := if_pos r.property
  have hn (r : {r : Fin 3 // ¬w r = .H}) :
      (if w r.val = .H then ∑ j, F r.val j else G r.val) = G r.val := if_neg r.property
  simp_rw [hp,hn]
  rw [Fintype.prod_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro κ _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun r => w r = .H)]
  have hp' (r : {r : Fin 3 // w r = .H}) :
      (if h : w r.val = .H then F r.val (κ ⟨r.val,h⟩) else G r.val) = F r.val (κ r) := by
    rw [dif_pos r.property]
  have hn' (r : {r : Fin 3 // ¬w r = .H}) :
      (if h : w r.val = .H then F r.val (κ ⟨r.val,h⟩) else G r.val) = G r.val := dif_neg r.property
  simp_rw [hp',hn']

theorem tripleBudgetRefinedComponent_continuous (w : MasterWord)
    (κ : TripleBudgetAssignment w) (r : Fin 3) (x : ℝ) (hx : 1≤x) :
    Continuous (tripleBudgetRefinedComponent w κ r x) := by
  unfold tripleBudgetRefinedComponent
  split_ifs
  · exact pairRHS_remainder_continuous _ x hx
  · exact tripleComponent_continuous _ x hx

theorem tripleBudgetRefined_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0<T) (hX : 1≤X) (hY : 1≤Y) (w : MasterWord)
    (κ : TripleBudgetAssignment w) : Integrable (tripleSmoothedIntegrand ω T
      (tripleBudgetRefinedComponent w κ 0 X) (tripleBudgetRefinedComponent w κ 1 Y)
      (tripleBudgetRefinedComponent w κ 2 (X*Y))) := by
  have hZ : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hc : Continuous (tripleSmoothedIntegrand ω T
      (tripleBudgetRefinedComponent w κ 0 X) (tripleBudgetRefinedComponent w κ 1 Y)
      (tripleBudgetRefinedComponent w κ 2 (X*Y))) := by
    unfold tripleSmoothedIntegrand
    exact (((Complex.continuous_ofReal.comp ((hω.comp (continuous_id.div_const T)).div_const T)).mul
      (tripleBudgetRefinedComponent_continuous w κ _ _ hX)).mul
      (tripleBudgetRefinedComponent_continuous w κ _ _ hY)).mul
      (tripleBudgetRefinedComponent_continuous w κ _ _ hZ).star
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  apply tripleMaster_support ω hs T hT
  intro hz
  exact ht (by simp [tripleSmoothedIntegrand,hz])

theorem tripleBudget_refinement_pointwise (ω : ℝ → ℝ) (T X Y t : ℝ) (w : MasterWord) :
    tripleWordIntegrand ω T X Y w t =
      ∑ κ : TripleBudgetAssignment w, tripleSmoothedIntegrand ω T
        (tripleBudgetRefinedComponent w κ 0 X) (tripleBudgetRefinedComponent w κ 1 Y)
        (tripleBudgetRefinedComponent w κ 2 (X*Y)) t := by
  classical
  let x : Fin 3 → ℝ := ![X,Y,X*Y]
  let F : Fin 3 → PairRemainderKind → ℂ := fun r j =>
    if r = 2 then star (pairRHSRemainder j (x r) t) else pairRHSRemainder j (x r) t
  let G : Fin 3 → ℂ := fun r =>
    if r = 2 then star (tripleComponent (w r) (x r) t) else tripleComponent (w r) (x r) t
  have hl (r : Fin 3) : (if w r = .H then ∑ j, F r j else G r) = G r := by
    by_cases hr : w r = .H
    · simp [F,G,hr,tripleComponent,pairRHSRemainderSum,← star_sum]
    · simp [hr]
  have hr (κ : TripleBudgetAssignment w) (r : Fin 3) :
      (if h : w r = .H then F r (κ ⟨r,h⟩) else G r) =
      if r = 2 then star (tripleBudgetRefinedComponent w κ r (x r) t)
        else tripleBudgetRefinedComponent w κ r (x r) t := by
    unfold tripleBudgetRefinedComponent
    split_ifs <;> simp_all [F,G]
  have he := tripleBudget_refinement_algebra w F G
  simp_rw [hl,hr] at he
  simp only [Fin.prod_univ_three] at he
  simp [G,x] at he
  simp only [starRingEnd_apply] at he
  unfold tripleWordIntegrand tripleSmoothedIntegrand
  calc
    _ = ((ω (t/T)/T:ℝ):ℂ)*(tripleComponent (w 0) X t*tripleComponent (w 1) Y t*
      star (tripleComponent (w 2) (X*Y) t)) := by ring
    _ = _ := by
      rw [he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro κ _
      ring

theorem tripleBudget_refinement (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (w : MasterWord) :
    tripleBudgetWordError ω T X Y w =
      ∑ κ : TripleBudgetAssignment w, tripleBudgetRefinedError ω T X Y w κ := by
  unfold tripleBudgetWordError tripleWordIntegral
  simp_rw [tripleBudget_refinement_pointwise]
  rw [integral_finsetSum _ (fun κ _ =>
    tripleBudgetRefined_integrable ω hω hs T X Y (by linarith) hX hY w κ),Finset.mul_sum]
  rfl

end
end HigherCorrelations
