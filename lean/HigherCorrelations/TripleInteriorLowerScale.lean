import HigherCorrelations.TripleRetainedEndpoints
import HigherCorrelations.TripleBudgetAsymptotic

/-! UNCONDITIONAL interior bounds, first with an independent lower scale R.
Every bound includes the closed height and scale endpoints. The constants are
chosen before the smoothing weight, height, and prime scales. -/
namespace HigherCorrelations
noncomputable section

/-- Elementary range consequences used before any logarithmic estimates. -/
theorem tripleInterior_range (T R X Y : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) (hZ : X*Y ≤ T/R) :
    1 ≤ X ∧ 1 ≤ Y ∧ X ≤ T ∧ Y ≤ T ∧ X*Y ≤ T ∧ R ≤ Real.sqrt (X*Y) := by
  have hx : 1 ≤ X := hR.trans hX
  have hy : 1 ≤ Y := hR.trans hY
  have hz : X*Y ≤ T := hZ.trans (div_le_self (by linarith) hR)
  refine ⟨hx,hy,?_,?_,hz,?_⟩
  · nlinarith
  · nlinarith
  · apply (Real.le_sqrt (by linarith) (by positivity)).mpr
    nlinarith [mul_le_mul hX hY (by linarith : 0 ≤ R) (by linarith : 0 ≤ X)]

theorem tripleInterior_log (T x : ℝ) (hT : 3 ≤ T) (hx : 1 ≤ x) (hxT : x ≤ T) :
    0 ≤ Real.log x ∧ Real.log x ≤ Real.log (2*T+2) := by
  exact ⟨Real.log_nonneg hx,Real.log_le_log (by linarith) (by linarith)⟩

/-- A common denominator bound for the two mixed contributions. -/
theorem tripleInterior_log_square (T R x : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hx : R ≤ x) (hxT : x ≤ T) :
    (1+Real.log x)/x^2 ≤ 2*Real.log (2*T+2)/R := by
  have hr : 0 < R := by linarith
  have hx1 : 1 ≤ x := hR.trans hx
  have hl := tripleInterior_log T x hT hx1 hxT
  have hL := tripleBudget_height_log T hT
  have hxr : R ≤ x^2 := by nlinarith
  exact (div_le_div_of_nonneg_right (by linarith : 1+Real.log x ≤ 2*Real.log (2*T+2))
    (sq_nonneg x)).trans (div_le_div_of_nonneg_left (by positivity) hr hxr)

theorem tripleInterior_diagonal_scale (T R X Y : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) (hZ : X*Y ≤ T/R) :
    tripleRetainedDiagonalScale X Y ≤ 4*Real.log (2*T+2)/R := by
  obtain ⟨hx,hy,hxt,hyt,hzt,hs⟩ := tripleInterior_range T R X Y hT hR hX hY hZ
  have h := add_le_add (tripleInterior_log_square T R Y hT hR hY hyt)
    (tripleInterior_log_square T R X hT hR hX hxt)
  exact h.trans_eq (by ring)

theorem tripleInterior_G (T R X Y : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) (hZ : X*Y ≤ T/R) :
    0 ≤ tripleRetainedG X Y ∧ tripleRetainedG X Y ≤ 4*Real.log (2*T+2)^2/R := by
  obtain ⟨hx,hy,hxt,hyt,hzt,hs⟩ := tripleInterior_range T R X Y hT hR hX hY hZ
  have hx0 : 0 < X := by linarith
  have hy0 : 0 < Y := by linarith
  have hz1 : 1 ≤ X*Y := by nlinarith
  have hlx := tripleInterior_log T X hT hx hxt
  have hly := tripleInterior_log T Y hT hy hyt
  have hlz := tripleInterior_log T (X*Y) hT hz1 hzt
  have hlxz : Real.log (X*(X*Y)) ≤ 2*Real.log (2*T+2) := by
    rw [Real.log_mul (ne_of_gt hx0) (by positivity)]
    linarith
  have hlyz : Real.log (Y*(X*Y)) ≤ 2*Real.log (2*T+2) := by
    rw [Real.log_mul (ne_of_gt hy0) (by positivity)]
    linarith
  have hlxz0 : 0 ≤ Real.log (X*(X*Y)) := Real.log_nonneg (by nlinarith)
  have hlyz0 : 0 ≤ Real.log (Y*(X*Y)) := Real.log_nonneg (by nlinarith)
  have hL := tripleBudget_height_log T hT
  have ha := mul_le_mul (tripleInterior_log_square T R Y hT hR hY hyt) hlxz
    hlxz0 (by positivity : 0 ≤ 2*Real.log (2*T+2)/R)
  have hb := mul_le_mul (tripleInterior_log_square T R X hT hR hX hxt) hlyz
    hlyz0 (by positivity : 0 ≤ 2*Real.log (2*T+2)/R)
  refine ⟨tripleRetainedG_nonneg X Y hx hy,?_⟩
  have hh := div_le_div_of_nonneg_right (add_le_add ha hb) (by norm_num : (0:ℝ) ≤ 2)
  unfold tripleRetainedG
  convert hh using 1 <;> ring

theorem tripleInterior_arch (T R X Y : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) (hZ : X*Y ≤ T/R) :
    0 ≤ Real.log T^3/(X*Y)^2 ∧
    Real.log T^3/(X*Y)^2 ≤ Real.log (2*T+2)^3/R := by
  obtain ⟨hx,hy,hxt,hyt,hzt,hs⟩ := tripleInterior_range T R X Y hT hR hX hY hZ
  have hl := tripleInterior_log T T hT (by linarith) le_rfl
  have hL := tripleBudget_height_log T hT
  have hz1 : 1 ≤ X*Y := by nlinarith
  have hrz : R ≤ X*Y := hX.trans (by nlinarith)
  have hrz2 : R ≤ (X*Y)^2 := by nlinarith
  refine ⟨div_nonneg (pow_nonneg hl.1 3) (sq_nonneg _),?_⟩
  exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hl.1 hl.2 3) (sq_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) (by linarith) hrz2)

theorem tripleInterior_resonance_scale (T R X Y : ℝ) (hT : 3 ≤ T) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) (hZ : X*Y ≤ T/R) :
    tripleResonanceScale (X*Y) ≤ Real.log (2*T+2)^3/R := by
  obtain ⟨hx,hy,hxt,hyt,hzt,hs⟩ := tripleInterior_range T R X Y hT hR hX hY hZ
  have hz1 : 1 ≤ X*Y := by nlinarith
  have hl0 : 0 ≤ Real.log (2*(X*Y)) := Real.log_nonneg (by nlinarith)
  have hl : Real.log (2*(X*Y)) ≤ Real.log (2*T+2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hL := tripleBudget_height_log T hT
  unfold tripleResonanceScale
  exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hl0 hl 3) (Real.sqrt_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) (by linarith) hs)

end
end HigherCorrelations
