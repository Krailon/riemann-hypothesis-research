import HigherCorrelations.TripleRetainedDefinitions
import HigherCorrelations.TripleMixedDiagonalEndpoints
import HigherCorrelations.TripleSmoothingMoment
import HigherCorrelations.TripleResonanceEndpoints

/-! UNCONDITIONAL exact retained-term algebra. No new infinite operation is
introduced. The original resonance sign and all coefficient definitions persist. -/
namespace HigherCorrelations
noncomputable section

theorem tripleRetainedDelta_ordered (a b : ℝ) (hab : a ≤ b) :
    tripleRetainedDelta a b = tripleBudgetDiagonal a b-tripleMixedDiagonalMain a b := by
  simp only [tripleRetainedDelta,min_eq_left hab,max_eq_right hab]

theorem tripleRetainedDelta_swap (a b : ℝ) : tripleRetainedDelta a b = tripleRetainedDelta b a := by
  rw [tripleRetainedDelta,tripleRetainedDelta,tripleBudgetDiagonal_swap a b,min_comm,max_comm]

theorem tripleRetainedG_swap (X Y : ℝ) : tripleRetainedG X Y = tripleRetainedG Y X := by
  unfold tripleRetainedG
  rw [mul_comm Y X]
  ring

theorem tripleRetainedDiagonalScale_swap (X Y : ℝ) :
    tripleRetainedDiagonalScale X Y = tripleRetainedDiagonalScale Y X := by
  unfold tripleRetainedDiagonalScale
  ring

theorem tripleRetainedErrorD_swap (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleRetainedErrorD ω T X Y = tripleRetainedErrorD ω T Y X := by
  unfold tripleRetainedErrorD
  rw [mul_comm Y X]
  ring

theorem tripleRetainedErrorJ_swap (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleRetainedErrorJ ω T X Y = tripleRetainedErrorJ ω T Y X := by
  unfold tripleRetainedErrorJ
  rw [tripleRetainedG_swap X Y]

theorem tripleRetainedG_nonneg (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    0 ≤ tripleRetainedG X Y := by
  have hZ : 1 ≤ X*Y := one_le_mul_of_one_le_of_one_le hX hY
  have hlX := Real.log_nonneg hX
  have hlY := Real.log_nonneg hY
  have hlXZ := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hX hZ)
  have hlYZ := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hY hZ)
  unfold tripleRetainedG
  positivity

theorem tripleRetainedDiagonalScale_nonneg (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    0 ≤ tripleRetainedDiagonalScale X Y := by
  have hlX := Real.log_nonneg hX
  have hlY := Real.log_nonneg hY
  unfold tripleRetainedDiagonalScale
  positivity

/-- Exact normalization of the two mixed-diagonal leading terms. -/
theorem tripleRetainedG_diagonal_main (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    tripleMixedDiagonalMain X (X*Y)/Y+tripleMixedDiagonalMain Y (X*Y)/X = tripleRetainedG X Y := by
  have hX0 : X ≠ 0 := by linarith
  have hY0 : Y ≠ 0 := by linarith
  have hx : X*Y/X=Y := by field_simp
  have hy : X*Y/Y=X := by field_simp
  unfold tripleMixedDiagonalMain tripleRetainedG
  rw [hx,hy]
  field_simp
  <;> ring

/-- The exact identity requires only the scale domain; analytic bounds are separate. -/
theorem tripleRetained_exact (ω : ℝ → ℝ) (T X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    tripleBudgetRetained ω T X Y =
      (tripleRetainedMain ω T X Y+tripleRetainedErrorD ω T X Y+
        tripleRetainedErrorJ ω T X Y-triplePrimeResonantMass X Y : ℝ) := by
  have hXZ : X ≤ X*Y := by nlinarith
  have hYZ : Y ≤ X*Y := by nlinarith
  have hg := tripleRetainedG_diagonal_main X Y hX hY
  unfold tripleBudgetRetained tripleRetainedMain tripleRetainedErrorD tripleRetainedErrorJ tripleSmoothingError
  rw [tripleRetainedDelta_ordered X (X*Y) hXZ,tripleRetainedDelta_ordered Y (X*Y) hYZ,← hg]
  congr 1
  ring

theorem tripleRetained_residual_norm (ω : ℝ → ℝ) (T X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    ‖tripleBudgetRetained ω T X Y-(tripleRetainedMain ω T X Y:ℂ)‖ =
      |tripleRetainedErrorD ω T X Y+tripleRetainedErrorJ ω T X Y-triplePrimeResonantMass X Y| := by
  rw [tripleRetained_exact ω T X Y hX hY,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  congr 1
  ring

end
end HigherCorrelations
