import HigherCorrelations.TripleBoundaryPointwise
import HigherCorrelations.TripleBoundaryRetainedBounds
import HigherCorrelations.TripleBoundaryHeight

/-! UNCONDITIONAL pointwise envelope for compact origin and axis profiles.
This estimate retains the product-scale decay needed at a nonzero axis frequency. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundary_G_height (T X Y : ℝ) (hT : 3 ≤ T) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hZ : X*Y ≤ T) : tripleRetainedG X Y ≤ 4*Real.log (2*T+2) := by
  have hx : 0 < X := by linarith
  have hy : 0 < Y := by linarith
  have hL := tripleBudget_height_log T hT
  have hxT : X ≤ T := (le_mul_of_one_le_right hx.le hY).trans hZ
  have hyT : Y ≤ T := (le_mul_of_one_le_left hy.le hX).trans hZ
  have hxL : Real.log X ≤ Real.log (2*T+2) := Real.log_le_log hx (by linarith)
  have hyL : Real.log Y ≤ Real.log (2*T+2) := Real.log_le_log hy (by linarith)
  have hx0 := Real.log_nonneg hX
  have hy0 := Real.log_nonneg hY
  have hiX : (1+Real.log X)/X^2 ≤ 1 :=
    (tripleBoundary_log_inverse X hX).trans (by simpa using one_div_le_one_div_of_le zero_lt_one hX)
  have hiY : (1+Real.log Y)/Y^2 ≤ 1 :=
    (tripleBoundary_log_inverse Y hY).trans (by simpa using one_div_le_one_div_of_le zero_lt_one hY)
  have h1 := mul_le_mul hiY (show Real.log X+Real.log Y/2 ≤ 2*Real.log (2*T+2) by linarith)
    (by positivity : 0 ≤ Real.log X+Real.log Y/2) (by norm_num : (0:ℝ) ≤ 1)
  have h2 := mul_le_mul hiX (show Real.log Y+Real.log X/2 ≤ 2*Real.log (2*T+2) by linarith)
    (by positivity : 0 ≤ Real.log Y+Real.log X/2) (by norm_num : (0:ℝ) ≤ 1)
  rw [tripleBoundary_G_logarithms X Y hx hy]
  convert add_le_add h1 h2 using 1 <;> ring

set_option maxHeartbeats 800000 in
theorem tripleBoundary_local_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T X Y : ℝ,
    0 ≤ W → (∀ u, ω u ≤ W) → 3 ≤ T → 1 ≤ X → 1 ≤ Y → X*Y ≤ T →
    ‖tripleQuadrantRemainder ω T X Y‖ ≤
      C*(1+W+fourierDerivativeL1 ω 1)*
        (Real.log (2*T+2)^2/(X*Y)+Real.log (2*T+2)+(X*Y)/T*Real.log (2*T+2)^4) := by
  obtain ⟨A,hA,H,hH,D,hD,h⟩ := tripleBoundary_pointwise
  let R := tripleResonanceDecayConstant
  have hR : 0 < R := tripleResonanceDecayConstant_pos
  refine ⟨82*A+3*H+2*D+8+3456*R,by positivity,?_⟩
  intro ω hω W T X Y hW hw hT hX hY hZT
  let L := Real.log (2*T+2)
  let Z := X*Y
  let V := 1+W+fourierDerivativeL1 ω 1
  have hL : 1 ≤ L := tripleBudget_height_log T hT
  have hL0 : 0 ≤ L := by linarith
  have hz : 1 ≤ Z := by dsimp [Z]; nlinarith
  have hz0 : 0 < Z := by linarith
  have ht0 : 0 < T := by linarith
  have hV : 1 ≤ V := by dsimp [V]; linarith [fourierDerivativeL1_nonneg ω 1]
  have hV0 : 0 ≤ V := by linarith
  have hW1 : 1+W ≤ V := by dsimp [V]; linarith [fourierDerivativeL1_nonneg ω 1]
  have hD1 : 1+fourierDerivativeL1 ω 1 ≤ V := by dsimp [V]; linarith
  have hsum : 1/X+1/Y ≤ 2 := by
    have hh := add_le_add (one_div_le_one_div_of_le zero_lt_one hX)
      (one_div_le_one_div_of_le zero_lt_one hY)
    norm_num at hh
    simpa only [one_div] using hh
  have hsquare : L^2/Z^2 ≤ L^2/Z :=
    div_le_div_of_nonneg_left (sq_nonneg L) hz0 (by nlinarith)
  have hcube : L^3/T ≤ 81*L :=
    (tripleBoundary_height_cube T hT).trans (by nlinarith)
  have hn := mul_le_mul (mul_le_mul_of_nonneg_left hD1 hA.le)
    (add_le_add (add_le_add hsquare hcube) (le_refl (Z/T*L^4)))
    (by positivity : 0 ≤ L^2/Z^2+L^3/T+Z/T*L^4) (by positivity : 0 ≤ A*V)
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hW1 hH.le)
    (add_le_add (mul_le_mul_of_nonneg_left hsum hL0) (le_refl (L^2/Z)))
    (by positivity : 0 ≤ L*(1/X+1/Y)+L^2/Z) (by positivity : 0 ≤ H*V)
  have hd : D*L*tripleRetainedDiagonalScale X Y ≤ 2*D*L := by
    have hh := mul_le_mul_of_nonneg_left ((tripleBoundary_diagonal_scale X Y hX hY).trans hsum)
      (show 0 ≤ D*L by positivity)
    nlinarith only [hh]
  have hg : 2*tripleRetainedG X Y/T ≤ 8*L := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (tripleBoundary_G_height T X Y hT hX hY hZT) (by norm_num : (0:ℝ) ≤ 2)) ht0.le).trans
    convert div_le_self (show 0 ≤ 8*L by positivity) (show 1 ≤ T by linarith) using 1 <;> ring
  have hr : R*tripleResonanceScale Z ≤ 3456*R*L := by
    have hs := (tripleBoundary_resonance_scale Z hz).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hz (by norm_num : -(1/4:ℝ) ≤ 0))
        (by norm_num : (0:ℝ) ≤ 3456))
    have hh := mul_le_mul_of_nonneg_left hs hR.le
    nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ 3456*R by positivity)]
  have hh0 := h ω hω W T X Y hW hw hT hX hY hZT
  apply hh0.trans
  have htotal := add_le_add (add_le_add (add_le_add (add_le_add hn hh) hd) hg) hr
  change _ ≤ A*V*(L^2/Z+81*L+Z/T*L^4)+H*V*(L*2+L^2/Z)+2*D*L+8*L+3456*R*L at htotal
  apply htotal.trans
  have ha : A*V*(L^2/Z+81*L+Z/T*L^4) ≤ 82*A*V*(L^2/Z+L+Z/T*L^4) := by
    nlinarith only [mul_nonneg (show 0 ≤ A*V by positivity) (show 0 ≤ L^2/Z by positivity),
      mul_nonneg (show 0 ≤ A*V by positivity) (show 0 ≤ Z/T*L^4 by positivity),
      mul_nonneg (show 0 ≤ A*V by positivity) hL0]
  have hb : H*V*(L*2+L^2/Z) ≤ 3*H*V*(L^2/Z+L+Z/T*L^4) := by
    nlinarith only [mul_nonneg (show 0 ≤ H*V by positivity) (show 0 ≤ L^2/Z by positivity),
      mul_nonneg (show 0 ≤ H*V by positivity) (show 0 ≤ Z/T*L^4 by positivity),
      mul_nonneg (show 0 ≤ H*V by positivity) hL0]
  have heL : L ≤ V*(L^2/Z+L+Z/T*L^4) := by
    have hh := mul_le_mul_of_nonneg_right hV (show 0 ≤ L^2/Z+L+Z/T*L^4 by positivity)
    have h1 : 0 ≤ L^2/Z := by positivity
    have h2 : 0 ≤ Z/T*L^4 := by positivity
    nlinarith only [hh,h1,h2]
  have hc := mul_le_mul_of_nonneg_left heL (show 0 ≤ 2*D+8+3456*R by positivity)
  change _ ≤ (82*A+3*H+2*D+8+3456*R)*V*(L^2/Z+L+Z/T*L^4)
  nlinarith only [ha,hb,hc]

end
end HigherCorrelations
