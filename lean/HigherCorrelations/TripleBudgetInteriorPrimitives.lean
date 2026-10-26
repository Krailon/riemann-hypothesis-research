import HigherCorrelations.TripleBudgetInteriorDefinitions
import HigherCorrelations.TripleBudgetWordBounds
import HigherCorrelations.TripleBudgetPrimeNorm

/-! UNCONDITIONAL interior primitives with an independent lower scale R >= 1.
Using R first makes the uniformity in epsilon explicit at the later substitution. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBudget_archConstant_nonneg : 0≤pairArchConstant := by
  have h := (norm_nonneg (pairArchError (1,0))).trans (pairArchError_bound 1 0 (by norm_num))
  simpa using h

theorem tripleBudgetHConstant_pos : 0<tripleBudgetHConstant := by
  unfold tripleBudgetHConstant
  linarith [tripleBudget_archConstant_nonneg,pairDSConstant_nonneg]

theorem tripleBudget_height_log (T : ℝ) (hT : 3≤T) : 1≤Real.log (2*T+2) := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<3) (by linarith : 3≤2*T+2)
  linarith [Real.log_three_gt_d9]

theorem tripleBudget_remainder_interior (T R x : ℝ) (hT : 3≤T)
    (hR : 1≤R) (hxR : R≤x) (hxT : x≤T) :
    tripleBudgetRemainderTotal T x ≤ tripleBudgetHConstant/R := by
  have hx : 1≤x := hR.trans hxR
  have hr : 0<R := by linarith
  have ht : 0<T := by linarith
  have hrt : R≤T := hxR.trans hxT
  have ha := div_le_div_of_nonneg_left tripleBudget_archConstant_nonneg hr hxR
  have hd := div_le_div_of_nonneg_left pairDSConstant_nonneg hr hxR
  have hs : Real.sqrt x≤T := (Real.sqrt_le_left ht.le).mpr (by nlinarith)
  have hp : 4*Real.sqrt x/(1+T^2)≤4/R := by
    apply (div_le_div_iff₀ (by positivity) hr).mpr
    have hh := mul_le_mul hs hrt hr.le ht.le
    nlinarith
  have hxpow : x^(-5/2:ℝ)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hv : 12*x^(-5/2:ℝ)/(T+2)≤12/R := by
    apply (div_le_div_iff₀ (by linarith) hr).mpr
    have hh := mul_le_mul_of_nonneg_right hxpow hr.le
    nlinarith
  change (∑ j, tripleBudgetRemainderBound j T x) ≤ _
  norm_num [tripleBudgetRemainderTotal,tripleBudgetRemainderBound,
    show (Finset.univ : Finset PairRemainderKind)={.arch,.ds,.pole,.trivial} by decide]
  unfold tripleBudgetHConstant
  have hh := add_le_add ha (add_le_add hd (add_le_add hp hv))
  convert hh using 1 <;> ring

theorem tripleBudget_letter_interior (C : ℝ) (hC : 0<C)
    (hmean : ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T x : ℝ,
      0≤W → (∀ u, ω u≤W) → 3≤T → 1≤x → x≤2*T →
        tripleBudgetPrimeL2 ω T x≤Real.sqrt (2*C*W*Real.log (2*x)))
    (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) (W T R x : ℝ)
    (hW : 0≤W) (hωW : ∀ u, ω u≤W) (hT : 3≤T) (hR : 1≤R) (hxR : R≤x) (hxT : x≤T)
    (l : MasterLetter) :
    tripleBudgetLetterNorm ω T x l ≤
      tripleBudgetInteriorNormConstant C*Real.sqrt (1+W)*Real.log (2*T+2) := by
  have hx : 1≤x := hR.trans hxR
  have hr : 0<R := by linarith
  have hL := tripleBudget_height_log T hT
  have hlog : Real.log (2*x)≤Real.log (2*T+2) := Real.log_le_log (by positivity) (by linarith)
  have hs : 1≤Real.sqrt (1+W) := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+W by linarith)
    simpa using h
  have hD : 1≤tripleBudgetInteriorNormConstant C := by
    unfold tripleBudgetInteriorNormConstant
    linarith [tripleBudgetHConstant_pos,Real.sqrt_nonneg (2*C)]
  have hDk : tripleBudgetHConstant≤tripleBudgetInteriorNormConstant C := by
    unfold tripleBudgetInteriorNormConstant
    linarith [Real.sqrt_nonneg (2*C)]
  have hDc : Real.sqrt (2*C)≤tripleBudgetInteriorNormConstant C := by
    unfold tripleBudgetInteriorNormConstant
    linarith [tripleBudgetHConstant_pos]
  cases l
  · apply (hmean ω hω W T x hW hωW hT hx (by linarith)).trans
    have hsq : 2*C*W*Real.log (2*x) ≤ (Real.sqrt (2*C)*Real.sqrt (1+W)*Real.log (2*T+2))^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by linarith : 0≤1+W)]
      have hll : Real.log (2*x)≤Real.log (2*T+2)^2 := by nlinarith
      have hh := mul_le_mul (show W≤1+W by linarith) hll
        (Real.log_nonneg (by linarith : 1≤2*x)) (by linarith : 0≤1+W)
      nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0≤2*C)]
    exact ((Real.sqrt_le_left (by positivity)).mpr hsq).trans
      (by gcongr)
  · change Real.log (2*T+2)/x≤_
    have hh : Real.log (2*T+2)/x≤Real.log (2*T+2) :=
      (div_le_self (by linarith) hx)
    apply hh.trans
    nlinarith [mul_le_mul hD hs (by norm_num : (0:ℝ)≤1) (by linarith : 0≤tripleBudgetInteriorNormConstant C)]
  · apply (tripleBudget_remainder_interior T R x hT hR hxR hxT).trans
    have hh : tripleBudgetHConstant/R≤tripleBudgetHConstant := div_le_self tripleBudgetHConstant_pos.le hR
    apply hh.trans
    have hsL : 1≤Real.sqrt (1+W)*Real.log (2*T+2) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsL (by linarith : 0≤tripleBudgetInteriorNormConstant C)]

end
end HigherCorrelations
