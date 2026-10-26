import HigherCorrelations.TripleBudgetInteriorPrimitives

/-! UNCONDITIONAL uniform sum of the nineteen remainder words. The 208
refinements are not counted again. The smoothing supremum enters only linearly. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBudget_range_geometry (T R X Y : ℝ) (hT : 3≤T) (hR : 1≤R)
    (hX : R≤X) (hY : R≤Y) (hZ : X*Y≤T/R) :
    (R≤X*Y) ∧ X≤T ∧ Y≤T ∧ X*Y≤T := by
  have hx : 1≤X := hR.trans hX
  have hy : 1≤Y := hR.trans hY
  have hxt : X≤X*Y := by nlinarith
  have hyt : Y≤X*Y := by nlinarith
  have hzt : X*Y≤T := hZ.trans (div_le_self (by linarith) hR)
  exact ⟨hX.trans hxt,hxt.trans hzt,hyt.trans hzt,hzt⟩

private theorem prod_three_one_small (a : Fin 3 → ℝ) (ha : ∀ i, 0≤a i)
    (B H : ℝ) (hB : 0≤B) (hH : 0≤H) (hb : ∀ i, a i≤B) (r : Fin 3) (hr : a r≤H) :
    (∏ i, a i)≤H*B^2 := by
  rw [Fin.prod_univ_three]
  fin_cases r
  · calc
      _ ≤ H*B*B := mul_le_mul (mul_le_mul hr (hb 1) (ha 1) hH) (hb 2) (ha 2) (mul_nonneg hH hB)
      _ = _ := by ring
  · calc
      _ ≤ B*H*B := mul_le_mul (mul_le_mul (hb 0) hr (ha 1) hB) (hb 2) (ha 2) (mul_nonneg hB hH)
      _ = _ := by ring
  · calc
      _ ≤ B*B*H := mul_le_mul (mul_le_mul (hb 0) (hb 1) (ha 1) hB) hr (ha 2) (mul_nonneg hB hB)
      _ = _ := by ring

theorem tripleBudget_remainder_words_uniform : ∃ K : ℝ, 0<K ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T R X Y : ℝ,
      0≤W → (∀ u, ω u≤W) → 3≤T → 1≤R → R≤X → R≤Y → X*Y≤T/R →
        ‖∑ w ∈ tripleBudgetRemainderWords, tripleBudgetWordError ω T X Y w‖ ≤
          K*(1+W)/R*Real.log (2*T+2)^2 := by
  obtain ⟨C,hC,hmean⟩ := tripleBudgetPrimeL2_uniform
  let D := tripleBudgetInteriorNormConstant C
  have hD : 0<D := by
    dsimp [D,tripleBudgetInteriorNormConstant]
    linarith [tripleBudgetHConstant_pos,Real.sqrt_nonneg (2*C)]
  refine ⟨19*tripleBudgetHConstant*D^2,by positivity [tripleBudgetHConstant_pos],?_⟩
  intro ω hω W T R X Y hW hωW hT hR hXR hYR hZT
  have hx : 1≤X := hR.trans hXR
  have hy : 1≤Y := hR.trans hYR
  obtain ⟨hZR,hXT,hYT,hZT'⟩ := tripleBudget_range_geometry T R X Y hT hR hXR hYR hZT
  have hRslot (r : Fin 3) : R≤(![X,Y,X*Y] r) := by fin_cases r <;> assumption
  have hTslot (r : Fin 3) : (![X,Y,X*Y] r)≤T := by fin_cases r <;> assumption
  have hL := tripleBudget_height_log T hT
  let B := D*Real.sqrt (1+W)*Real.log (2*T+2)
  have hB : 0≤B := by dsimp [B]; positivity
  have hb (w : MasterWord) (hw : w∈tripleBudgetRemainderWords) :
      ‖tripleBudgetWordError ω T X Y w‖ ≤
        (tripleBudgetHConstant/R)*B^2 := by
    have hh : tripleWordHasH w=true := (Finset.mem_filter.mp hw).2
    obtain ⟨r,hr⟩ := of_decide_eq_true hh
    apply (tripleBudget_word_bound ω hω T X Y hT hx hy w hh).trans
    apply prod_three_one_small _
      (fun i => tripleBudgetLetterNorm_nonneg ω T _ hT (hR.trans (hRslot i)) _) B (tripleBudgetHConstant/R)
      hB (by positivity [tripleBudgetHConstant_pos])
      (fun i => tripleBudget_letter_interior C hC hmean ω hω W T R _ hW hωW hT hR (hRslot i) (hTslot i) _) r
    rw [hr]
    exact tripleBudget_remainder_interior T R _ hT hR (hRslot r) (hTslot r)
  calc
    _ ≤ ∑ w ∈ tripleBudgetRemainderWords, ‖tripleBudgetWordError ω T X Y w‖ := norm_sum_le _ _
    _ ≤ ∑ _w ∈ tripleBudgetRemainderWords, (tripleBudgetHConstant/R)*B^2 := Finset.sum_le_sum hb
    _ = _ := by
      rw [Finset.sum_const,tripleBudget_remainder_count]
      simp only [nsmul_eq_mul,Nat.cast_ofNat,B,mul_pow,Real.sq_sqrt (by linarith : 0≤1+W)]
      ring

end
end HigherCorrelations
