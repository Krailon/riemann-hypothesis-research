import HigherCorrelations.PairDiagonalAlgebra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! UNCONDITIONAL. Exact antiderivatives for the diagonal weight and its model. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

/-- Primitive of u log u on the positive half-line. -/
theorem pairDiagonal_head_primitive (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => t^2*Real.log t/2-t^2/4) (u*Real.log u) u := by
  convert ((((hasDerivAt_id u).pow 2).mul (Real.hasDerivAt_log hu.ne')).div_const 2).sub
    (((hasDerivAt_id u).pow 2).div_const 4) using 1 <;> (try funext t) <;> dsimp <;> field_simp <;> ring

/-- Primitive of log u / u^3 on the positive half-line. -/
theorem pairDiagonal_tail_primitive (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => -(2*Real.log t+1)/(4*t^2)) (Real.log u/u^3) u := by
  convert (((((Real.hasDerivAt_log hu.ne').const_mul 2).add_const 1).neg).div
    (((hasDerivAt_id u).pow 2).const_mul 4) (by dsimp; positivity)) using 1 <;>
    (try funext t) <;> dsimp <;> field_simp <;> ring

theorem pairDiagonal_head_integral (X : ℝ) (hX : 1 ≤ X) :
    (∫ u in (1:ℝ)..X, u*Real.log u) = X^2*Real.log X/2-X^2/4+1/4 := by
  have hc : ContinuousOn (fun u : ℝ => u*Real.log u) (Set.uIcc 1 X) := by
    apply continuousOn_id.mul (Real.continuousOn_log.mono _)
    intro u hu
    rw [Set.uIcc_of_le hX] at hu
    exact ne_of_gt (by linarith [hu.1])
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => pairDiagonal_head_primitive u (by
      rw [Set.uIcc_of_le hX] at hu; linarith [hu.1])) hc.intervalIntegrable
  simpa using he

theorem pairDiagonal_tail_integral (X Y : ℝ) (hX : 0 < X) (hXY : X ≤ Y) :
    (∫ u in X..Y, Real.log u/u^3) =
      (2*Real.log X+1)/(4*X^2)-(2*Real.log Y+1)/(4*Y^2) := by
  have hu0 (u : ℝ) (hu : u ∈ Set.uIcc X Y) : 0 < u := by
    rw [Set.uIcc_of_le hXY] at hu; exact hX.trans_le hu.1
  have hc : ContinuousOn (fun u : ℝ => Real.log u/u^3) (Set.uIcc X Y) :=
    (Real.continuousOn_log.mono (fun u hu => (hu0 u hu).ne')).div
      (continuousOn_id.pow 3) (fun u hu => pow_ne_zero _ (hu0 u hu).ne')
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => pairDiagonal_tail_primitive u (hu0 u hu)) hc.intervalIntegrable
  convert he using 1 <;> ring

/-- Exact integral used to dominate the upper-tail error. -/
theorem pairDiagonal_inverse_cube_integral (X Y : ℝ) (hX : 0 < X) (hXY : X ≤ Y) :
    (∫ u in X..Y, (1:ℝ)/u^3) = 1/(2*X^2)-1/(2*Y^2) := by
  have hu0 (u : ℝ) (hu : u ∈ Set.uIcc X Y) : 0 < u := by
    rw [Set.uIcc_of_le hXY] at hu; exact hX.trans_le hu.1
  have hc : ContinuousOn (fun u : ℝ => 1/u^3) (Set.uIcc X Y) :=
    continuousOn_const.div (continuousOn_id.pow 3) (fun u hu => pow_ne_zero _ (hu0 u hu).ne')
  have hd (u : ℝ) (hu : 0 < u) : HasDerivAt (fun t : ℝ => -(1:ℝ)/(2*t^2)) (1/u^3) u := by
    convert (hasDerivAt_const u (-(1:ℝ))).div
      (((hasDerivAt_id u).pow 2).const_mul 2) (by dsimp; positivity) using 1 <;>
      (try funext t) <;> dsimp <;> field_simp <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u (hu0 u hu)) hc.intervalIntegrable
  convert he using 1 <;> ring

end
end HigherCorrelations
