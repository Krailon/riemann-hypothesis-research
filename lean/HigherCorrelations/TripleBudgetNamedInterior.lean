import HigherCorrelations.TripleBudgetInteriorErrors

/-! UNCONDITIONAL combination of the eight separately named non-remainder errors.
R is independent of epsilon; the resulting constant is absolute. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBudgetMixedConstant_nonneg : 0≤tripleBudgetMixedConstant := by
  unfold tripleBudgetMixedConstant
  positivity [tripleDyadicConstant_pos 3]

theorem tripleBudgetCubicConstant_nonneg : 0≤tripleBudgetCubicConstant := by
  unfold tripleBudgetCubicConstant
  positivity [triplePrimeMassConstant_pos]

theorem tripleBudgetNamedConstant_pos : 0<tripleBudgetNamedConstant := by
  unfold tripleBudgetNamedConstant
  positivity [tripleBudgetMixedConstant_nonneg,tripleBudgetCubicConstant_nonneg]

theorem tripleBudget_named_interior (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T R X Y : ℝ) (hT : 3≤T) (hR : 1≤R) (hXR : R≤X) (hYR : R≤Y) (hZ : X*Y≤T/R) :
    ‖∑ e : TripleBudgetError, tripleBudgetError ω T X Y e‖ ≤
      tripleBudgetNamedConstant*(1+fourierDerivativeL1 ω 1)/R*Real.log (2*T+2)^4 := by
  let L := Real.log (2*T+2)
  let V := 1+fourierDerivativeL1 ω 1
  let B := V/R*L^4
  have ht : 0<T := by linarith
  have hr : 0<R := by linarith
  have hx : 1≤X := hR.trans hXR
  have hy : 1≤Y := hR.trans hYR
  obtain ⟨hzR,hXT,hYT,hZT⟩ := tripleBudget_range_geometry T R X Y hT hR hXR hYR hZ
  have hz : 1≤X*Y := hR.trans hzR
  have hrt : R≤T := hXR.trans hXT
  have hL : 1≤L := tripleBudget_height_log T hT
  have hV : 1≤V := by dsimp [V]; linarith [fourierDerivativeL1_nonneg ω 1]
  have hB : 0≤B := by dsimp [B]; positivity
  have hL2 : L^2≤L^4 := pow_le_pow_right₀ hL (by omega)
  have hL3 : L^3≤L^4 := pow_le_pow_right₀ hL (by omega)
  have hrT : 1/T≤1/R := one_div_le_one_div_of_le hr hrt
  have hzT : (X*Y)/T≤1/R := (div_le_div_iff₀ ht hr).mpr (by
    have hh := (le_div_iff₀ hr).mp hZ
    nlinarith)
  have hzR2 : 1/(X*Y)^2≤1/R := one_div_le_one_div_of_le hr (by nlinarith)
  have hΩ1 : tripleBudgetOmega ω T 1≤V*L := (tripleBudgetOmega_height ω hω T hT).1
  have hΩ2 : tripleBudgetOmega ω T 2≤2*V*L^2 := (tripleBudgetOmega_height ω hω T hT).2
  have hΩ0 (r : ℕ) : 0≤tripleBudgetOmega ω T r := fourierDerivativeL1_nonneg _ _
  have hsmall : 5*tripleBudgetOmega ω T 2/T≤10*B := by
    calc
      _ ≤ 5*(2*V*L^2)/T := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΩ2 (by norm_num)) ht.le
      _ = 10*V*(1/T)*L^2 := by ring
      _ ≤ 10*V*(1/R)*L^4 := by gcongr
      _ = _ := by dsimp [B]; ring
  have harch : ‖tripleBudgetError ω T X Y .archcube‖≤B := by
    apply (tripleBudget_archcube_bounds ω hω T X Y hT).2.trans
    have hq : 0≤Real.log T^3 := pow_nonneg (Real.log_nonneg (by linarith)) 3
    calc
      _ ≤ L^3/(X*Y)^2 := div_le_div_of_nonneg_right (by dsimp [L]; linarith) (sq_nonneg _)
      _ ≤ L^4*(1/R) := by
        convert mul_le_mul hL3 hzR2 (by positivity) (by positivity) using 1 <;> ring
      _ ≤ V/R*L^4 := by
        have hh := mul_le_mul_of_nonneg_right hV (by positivity : 0≤L^4/R)
        convert hh using 1 <;> ring
  have hppa : ‖tripleBudgetError ω T X Y .PPA‖≤(triplePrimeMassConstant^2/Real.log 4)*B := by
    apply (tripleBudget_PPA_bound ω hω T X Y hT hx hy).trans
    have hm := tripleBudget_mass_pair_height T X Y hT hx hy hXT hYT
    calc
      _ = (triplePrimeMass X*triplePrimeMass Y/(X*Y))*tripleBudgetOmega ω T 1*(1/T)/Real.log 4 := by ring
      _ ≤ (triplePrimeMassConstant^2*L^2)*(V*L)*(1/R)/Real.log 4 := by
        apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
        apply mul_le_mul _ hrT (by positivity) (by positivity)
        exact mul_le_mul hm hΩ1 (hΩ0 1) (by positivity)
      _ = (triplePrimeMassConstant^2/Real.log 4)*V/R*L^3 := by ring
      _ ≤ (triplePrimeMassConstant^2/Real.log 4)*V/R*L^4 := by gcongr
      _ = _ := by dsimp [B]; ring
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
      _ ≤ tripleBudgetMixedConstant*V*(1/R)*L^4 := by gcongr
      _ = _ := by dsimp [B]; ring
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
      _ ≤ tripleBudgetCubicConstant*V*(1/R)*L^4 := by gcongr
      _ = _ := by dsimp [B]; ring
  obtain ⟨hpaa,hapa,haap⟩ := tripleBudget_single_words_height ω hω T X Y hT hx hy
  have hpaa' := hpaa.trans hsmall
  have hapa' := hapa.trans hsmall
  have haap' := haap.trans hsmall
  apply (norm_sum_le _ _).trans
  have hu : (Finset.univ : Finset TripleBudgetError) =
      {.archcube,.PPA,.PAA,.APA,.AAP,.PAPoff,.APPoff,.PPPoff} := by decide
  rw [hu]
  norm_num only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    reduceCtorEq,or_self,not_false_eq_true]
  change _ ≤ tripleBudgetNamedConstant*V/R*L^4
  rw [show tripleBudgetNamedConstant*V/R*L^4=tripleBudgetNamedConstant*B by dsimp [B]; ring]
  unfold tripleBudgetNamedConstant
  nlinarith

end
end HigherCorrelations
