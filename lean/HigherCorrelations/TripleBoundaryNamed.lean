import HigherCorrelations.TripleBoundaryArch
import HigherCorrelations.TripleBudgetNamedInterior

/-! UNCONDITIONAL named-error envelope that preserves the origin-layer decay
and the upper product scale separately. All eight non-H errors occur once. -/
namespace HigherCorrelations
noncomputable section

set_option maxHeartbeats 800000 in
theorem tripleBoundary_named_bound : ∃ K : ℝ, 0<K ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ T X Y : ℝ,
    3≤T → 1≤X → 1≤Y → X*Y≤T →
    (∑ e : TripleBudgetError, ‖tripleBudgetError ω T X Y e‖) ≤
    K*(1+fourierDerivativeL1 ω 1)*(Real.log (2*T+2)^2/(X*Y)^2+
      Real.log (2*T+2)^3/T+(X*Y)/T*Real.log (2*T+2)^4) := by
  let K := 3*Real.log 3+triplePrimeMassConstant^2/Real.log 4+30+
    2*tripleBudgetMixedConstant+tripleBudgetCubicConstant
  have hK : 0<K := by
    dsimp [K]
    positivity [tripleBudgetMixedConstant_nonneg,tripleBudgetCubicConstant_nonneg]
  refine ⟨K,hK,?_⟩
  intro ω hω T X Y hT hx hy hZT
  let L := Real.log (2*T+2)
  let V := 1+fourierDerivativeL1 ω 1
  let B := V*(L^2/(X*Y)^2+L^3/T+(X*Y)/T*L^4)
  have ht : 0<T := by linarith
  have hL : 1≤L := tripleBudget_height_log T hT
  have hV : 1≤V := by dsimp [V]; linarith [fourierDerivativeL1_nonneg ω 1]
  have hB : 0≤B := by dsimp [B]; positivity
  have hz : 1≤X*Y := one_le_mul_of_one_le_of_one_le hx hy
  have hXT : X≤T := (show X≤X*Y by nlinarith).trans hZT
  have hYT : Y≤T := (show Y≤X*Y by nlinarith).trans hZT
  have harchB : V*(L^2/(X*Y)^2)≤B := by
    dsimp [B]
    exact mul_le_mul_of_nonneg_left (by linarith [show 0≤L^3/T by positivity, show 0≤(X*Y)/T*L^4 by positivity] : L^2/(X*Y)^2≤L^2/(X*Y)^2+L^3/T+(X*Y)/T*L^4) (by linarith)
  have htime : V/T*L^3≤B := by
    rw [show V/T*L^3=V*(L^3/T) by ring]
    dsimp [B]
    apply mul_le_mul_of_nonneg_left _ (show 0≤V by linarith)
    have hp : 0≤L^2/(X*Y)^2 := by positivity
    have hz' : 0≤(X*Y)/T*L^4 := by positivity
    linarith only [hp,hz']
  have hlarge : V*((X*Y)/T)*L^4≤B := by
    dsimp [B]
    nlinarith only [mul_nonneg (show 0≤V by linarith) (show 0≤L^2/(X*Y)^2 by positivity),
      mul_nonneg (show 0≤V by linarith) (show 0≤L^3/T by positivity)]
  have hΩ1 : tripleBudgetOmega ω T 1≤V*L := (tripleBudgetOmega_height ω hω T hT).1
  have hΩ2 : tripleBudgetOmega ω T 2≤2*V*L^2 := (tripleBudgetOmega_height ω hω T hT).2
  have hΩ0 (r : ℕ) : 0≤tripleBudgetOmega ω T r := fourierDerivativeL1_nonneg _ _
  have hsmall : 5*tripleBudgetOmega ω T 2/T≤10*B := by
    calc
      _ ≤ 5*(2*V*L^2)/T := by gcongr
      _ = 10*(V/T*L^2) := by ring
      _ ≤ 10*(V/T*L^3) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (show 2≤3 by omega)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left htime (by norm_num)
  have harch : ‖tripleBudgetError ω T X Y .archcube‖≤(3*Real.log 3)*B := by
    apply (tripleBoundary_archcube ω hω T X Y hT).trans
    calc
      _ = (3*Real.log 3)*(L^2/(X*Y)^2) := by ring
      _ ≤ (3*Real.log 3)*(V*(L^2/(X*Y)^2)) := by gcongr; exact le_mul_of_one_le_left (by positivity) hV
      _ ≤ _ := mul_le_mul_of_nonneg_left harchB (by positivity)
  have hppa : ‖tripleBudgetError ω T X Y .PPA‖≤(triplePrimeMassConstant^2/Real.log 4)*B := by
    apply (tripleBudget_PPA_bound ω hω T X Y hT hx hy).trans
    have hm := tripleBudget_mass_pair_height T X Y hT hx hy hXT hYT
    calc
      _ = (triplePrimeMass X*triplePrimeMass Y/(X*Y))*tripleBudgetOmega ω T 1*(1/T)/Real.log 4 := by ring
      _ ≤ (triplePrimeMassConstant^2*L^2)*(V*L)*(1/T)/Real.log 4 := by
        apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hm hΩ1 (hΩ0 1) (by positivity)
      _ = (triplePrimeMassConstant^2/Real.log 4)*(V/T*L^3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htime (by positivity)
  have hmix (a b : ℝ) (ha : 1≤a) (hb : 1≤b) (haT : a≤T)
      (hab : a≤X*Y) :
      tripleBudgetMixedConstant*(tripleBudgetOmega ω T 1/T)*(a/Real.sqrt b)*
        Real.sqrt (Real.log (2*a)^3*Real.log (2*(X*Y))^3) ≤ tripleBudgetMixedConstant*B := by
    have hs : 1≤Real.sqrt b := by simpa using Real.sqrt_le_sqrt hb
    have hab' : a/Real.sqrt b≤X*Y := (div_le_self (by linarith) hs).trans hab
    have hlog := tripleBudget_mixed_log_height T a (X*Y) hT ha hz haT hZT
    have hc := tripleBudgetMixedConstant_nonneg
    calc
      _ ≤ tripleBudgetMixedConstant*((V*L)/T)*(X*Y)*L^3 := by gcongr
      _ = tripleBudgetMixedConstant*V*((X*Y)/T)*L^4 := by ring
      _ ≤ tripleBudgetMixedConstant*B := by
        convert mul_le_mul_of_nonneg_left hlarge hc using 1 <;> ring
  have hpap : ‖tripleBudgetError ω T X Y .PAPoff‖≤tripleBudgetMixedConstant*B :=
    (tripleBudget_PAPoff_rate ω hω T X Y hT hx hy).trans
      (hmix X Y hx hy hXT (by nlinarith))
  have happ : ‖tripleBudgetError ω T X Y .APPoff‖≤tripleBudgetMixedConstant*B :=
    (tripleBudget_APPoff_rate ω hω T X Y hT hx hy).trans
      (hmix Y X hy hx hYT (by nlinarith))
  have hppp : ‖tripleBudgetError ω T X Y .PPPoff‖≤tripleBudgetCubicConstant*B := by
    apply (tripleBudget_PPPoff_rate ω hω T X Y hT hx hy).trans
    have hc := tripleBudgetCubicConstant_nonneg
    have hw : fourierDerivativeL1 ω 1≤V := by dsimp [V]; linarith
    have hlog := (tripleBudget_coefficient_log_height T (X*Y) hT hz hZT).2
    have hlog0 := (tripleBudget_coefficient_log_height T (X*Y) hT hz hZT).1
    change tripleBudgetCubicConstant*fourierDerivativeL1 ω 1*(X*Y)*Real.log (2*(X*Y))^4/T≤_
    calc
      _ = tripleBudgetCubicConstant*fourierDerivativeL1 ω 1*((X*Y)/T)*Real.log (2*(X*Y))^4 := by ring
      _ ≤ tripleBudgetCubicConstant*V*((X*Y)/T)*L^4 := by gcongr
      _ ≤ tripleBudgetCubicConstant*B := by
        convert mul_le_mul_of_nonneg_left hlarge hc using 1 <;> ring
  obtain ⟨hpaa,hapa,haap⟩ := tripleBudget_single_words_height ω hω T X Y hT hx hy
  have hpaa' := hpaa.trans hsmall
  have hapa' := hapa.trans hsmall
  have haap' := haap.trans hsmall
  have hu : (Finset.univ : Finset TripleBudgetError) =
      {.archcube,.PPA,.PAA,.APA,.AAP,.PAPoff,.APPoff,.PPPoff} := by decide
  rw [hu]
  norm_num only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    reduceCtorEq,or_self,not_false_eq_true]
  change _ ≤ K*V*(L^2/(X*Y)^2+L^3/T+(X*Y)/T*L^4)
  rw [show K*V*(L^2/(X*Y)^2+L^3/T+(X*Y)/T*L^4)=K*B by dsimp [B]; ring]
  change _ ≤ (3*Real.log 3+triplePrimeMassConstant^2/Real.log 4+30+
    2*tripleBudgetMixedConstant+tripleBudgetCubicConstant)*B
  nlinarith only [harch,hppa,hpaa',hapa',haap',hpap,happ,hppp]

end
end HigherCorrelations
