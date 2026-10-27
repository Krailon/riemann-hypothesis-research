import HigherCorrelations.TripleInteriorLowerScale

/-! UNCONDITIONAL bounds for each retained contribution, and the native full-zero
observable. The absolute constants remain existential through the diagonal and
prime mean-square inputs; no numerical effectiveness is asserted. -/
namespace HigherCorrelations
noncomputable section

theorem tripleInterior_main (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T R X Y : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) (hZ : X*Y ≤ T/R) :
    0 ≤ tripleRetainedMain ω T X Y ∧
    tripleRetainedMain ω T X Y ≤ 9*Real.log (2*T+2)^3/R := by
  have ha := tripleInterior_arch T R X Y hT hR hX hY hZ
  have hg := tripleInterior_G T R X Y hT hR hX hY hZ
  have hm := tripleSmoothingMean_bounds ω hω
  have hl := tripleInterior_log T T hT (by linarith) le_rfl
  have hl2 := tripleInterior_log T 2 hT (by norm_num) (by linarith)
  have hL := tripleBudget_height_log T hT
  have hq : Real.log T+tripleSmoothingMean ω ≤ 2*Real.log (2*T+2) := by linarith
  have hh := mul_le_mul hq hg.2 hg.1 (by positivity : 0 ≤ 2*Real.log (2*T+2))
  refine ⟨add_nonneg ha.1 (mul_nonneg (by linarith) hg.1),?_⟩
  exact (add_le_add ha.2 hh).trans_eq (by ring)

theorem tripleInterior_diagonal_error (C : ℝ) (hC : 0 ≤ C)
    (ω : ℝ → ℝ) (T R X Y : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) (hZ : X*Y ≤ T/R)
    (hD : |tripleRetainedErrorD ω T X Y| ≤ C*Real.log (2*T+2)*tripleRetainedDiagonalScale X Y) :
    |tripleRetainedErrorD ω T X Y| ≤ 4*C*Real.log (2*T+2)^3/R := by
  have hL := tripleBudget_height_log T hT
  have hb := tripleInterior_diagonal_scale T R X Y hT hR hX hY hZ
  have hp : Real.log (2*T+2)^2 ≤ Real.log (2*T+2)^3 := pow_le_pow_right₀ hL (by omega)
  calc
    _ ≤ C*Real.log (2*T+2)*(4*Real.log (2*T+2)/R) :=
      hD.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = (4*C/R)*Real.log (2*T+2)^2 := by ring
    _ ≤ (4*C/R)*Real.log (2*T+2)^3 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem tripleInterior_smoothing_error (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T R X Y : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) (hZ : X*Y ≤ T/R) :
    0 ≤ tripleRetainedErrorJ ω T X Y ∧
    tripleRetainedErrorJ ω T X Y ≤ 8*Real.log (2*T+2)^3/R := by
  have hj := tripleRetainedErrorJ_bounds ω hω T X Y (by linarith) (hR.trans hX) (hR.trans hY)
  have hg := tripleInterior_G T R X Y hT hR hX hY hZ
  have hL := tripleBudget_height_log T hT
  have hp : Real.log (2*T+2)^2 ≤ Real.log (2*T+2)^3 := pow_le_pow_right₀ hL (by omega)
  refine ⟨hj.1,?_⟩
  calc
    _ ≤ 2*tripleRetainedG X Y/T := hj.2
    _ ≤ 2*tripleRetainedG X Y := div_le_self (mul_nonneg (by norm_num) hg.1) (by linarith)
    _ ≤ 2*(4*Real.log (2*T+2)^2/R) := mul_le_mul_of_nonneg_left hg.2 (by norm_num)
    _ = (8/R)*Real.log (2*T+2)^2 := by ring
    _ ≤ (8/R)*Real.log (2*T+2)^3 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem tripleInterior_resonance (T R X Y : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) (hZ : X*Y ≤ T/R) :
    0 ≤ triplePrimeResonantMass X Y ∧
    triplePrimeResonantMass X Y ≤ tripleResonanceDecayConstant*Real.log (2*T+2)^3/R := by
  have hr := triplePrimeResonantMass_decay X Y (hR.trans hX) (hR.trans hY)
  refine ⟨hr.1,?_⟩
  exact (hr.2.trans (mul_le_mul_of_nonneg_left
    (tripleInterior_resonance_scale T R X Y hT hR hX hY hZ)
    tripleResonanceDecayConstant_pos.le)).trans_eq (by ring)

theorem tripleInterior_retained_lower_scale : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ T R X Y : ℝ,
    3 ≤ T → 1 ≤ R → R ≤ X → R ≤ Y → X*Y ≤ T/R →
    ‖tripleBudgetRetained ω T X Y‖ ≤ C*Real.log (2*T+2)^3/R := by
  obtain ⟨K,hK,hD⟩ := tripleRetainedErrorD_uniform
  refine ⟨17+4*K+tripleResonanceDecayConstant,by linarith [tripleResonanceDecayConstant_pos],?_⟩
  intro ω hω T R X Y hT hR hX hY hZ
  have hx := hR.trans hX
  have hy := hR.trans hY
  have hm := tripleInterior_main ω hω T R X Y hT hR hX hY hZ
  have hd := tripleInterior_diagonal_error K hK.le ω T R X Y hT hR hX hY hZ (hD ω T X Y hω hT hx hy)
  have hj := tripleInterior_smoothing_error ω hω T R X Y hT hR hX hY hZ
  have hr := tripleInterior_resonance T R X Y hT hR hX hY hZ
  rw [tripleRetained_exact ω T X Y hx hy,Complex.norm_real]
  calc
    _ ≤ |tripleRetainedMain ω T X Y|+|tripleRetainedErrorD ω T X Y|+
        |tripleRetainedErrorJ ω T X Y|+|triplePrimeResonantMass X Y| :=
      (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ = tripleRetainedMain ω T X Y+|tripleRetainedErrorD ω T X Y|+
        tripleRetainedErrorJ ω T X Y+triplePrimeResonantMass X Y := by
      rw [abs_of_nonneg hm.1,abs_of_nonneg hj.1,abs_of_nonneg hr.1]
    _ ≤ _ := (add_le_add (add_le_add (add_le_add hm.2 hd) hj.2) hr.2).trans_eq (by ring)

theorem tripleInterior_retained_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ ε T X Y : ℝ,
    0 < ε → ε < 1/3 → 3 ≤ T → T^ε ≤ X → T^ε ≤ Y → X*Y ≤ T^(1-ε) →
    ‖tripleBudgetRetained ω T X Y‖ ≤ C*T^(-ε)*Real.log (2*T+2)^3 := by
  obtain ⟨C,hC,h⟩ := tripleInterior_retained_lower_scale
  refine ⟨C,hC,?_⟩
  intro ω hω ε T X Y hε _hεupper hT hX hY hZ
  have ht : 0 < T := by linarith
  have hR : 1 ≤ T^ε := Real.one_le_rpow (by linarith) hε.le
  have hz : X*Y ≤ T/T^ε := by simpa only [Real.rpow_sub ht,Real.rpow_one] using hZ
  convert h ω hω T (T^ε) X Y hT hR hX hY hz using 1
  rw [Real.rpow_neg ht.le]
  ring

theorem tripleInterior_observable_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W ε T X Y : ℝ,
    0 ≤ W → (∀ u, ω u ≤ W) → 0 < ε → ε < 1/3 → 3 ≤ T →
    T^ε ≤ X → T^ε ≤ Y → X*Y ≤ T^(1-ε) →
    ‖tripleMasterObservable ω T X Y‖ ≤ C*tripleBudgetEnvelope ε W (fourierDerivativeL1 ω 1) T := by
  obtain ⟨A,hA,herr⟩ := tripleBudget_uniform_asymptotic
  obtain ⟨B,hB,hmain⟩ := tripleInterior_retained_bound
  refine ⟨A+B,by linarith,?_⟩
  intro ω hω W ε T X Y hW hωW hε hεupper hT hX hY hZ
  have he := herr ω hω W ε T X Y hW hωW hε hεupper hT hX hY hZ
  have hm := hmain ω hω ε T X Y hε hεupper hT hX hY hZ
  have hL := tripleBudget_height_log T hT
  have hd := fourierDerivativeL1_nonneg ω 1
  have hp : Real.log (2*T+2)^3 ≤ Real.log (2*T+2)^4 := pow_le_pow_right₀ hL (by omega)
  have hb : B*T^(-ε)*Real.log (2*T+2)^3 ≤ B*tripleBudgetEnvelope ε W (fourierDerivativeL1 ω 1) T := by
    unfold tripleBudgetEnvelope
    calc
      _ ≤ B*T^(-ε)*Real.log (2*T+2)^4 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ B*((1+W+fourierDerivativeL1 ω 1)*T^(-ε)*Real.log (2*T+2)^4) := by
        have hh : 1 ≤ 1+W+fourierDerivativeL1 ω 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ B*T^(-ε)*Real.log (2*T+2)^4)]
  calc
    _ ≤ ‖tripleMasterObservable ω T X Y-tripleBudgetRetained ω T X Y‖+‖tripleBudgetRetained ω T X Y‖ := by simpa only [add_comm] using norm_le_insert' (tripleMasterObservable ω T X Y) (tripleBudgetRetained ω T X Y)
    _ ≤ _ := (add_le_add he (hm.trans hb)).trans_eq (by ring)

end
end HigherCorrelations
