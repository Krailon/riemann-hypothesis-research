import HigherCorrelations.TripleRetainedEvaluation
import HigherCorrelations.TripleQuadrantDefinitions
import HigherCorrelations.TripleTestPhase

/-! UNCONDITIONAL exact exponential profiles of the retained leading expression.
These algebraic identities include zero frequencies and contain no limit claim. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundary_G_logarithms (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    tripleRetainedG X Y =
      (1+Real.log Y)*(Real.log X+Real.log Y/2)/Y^2 +
      (1+Real.log X)*(Real.log Y+Real.log X/2)/X^2 := by
  unfold tripleRetainedG
  rw [Real.log_mul hX.ne' (mul_pos hX hY).ne',
    Real.log_mul hY.ne' (mul_pos hX hY).ne',Real.log_mul hX.ne' hY.ne']
  ring

private theorem inverse_exp_square (v : ℝ) : (Real.exp v)^2 * Real.exp (-(2*v)) = 1 := by
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [← Real.exp_add]
  ring_nf
  exact Real.exp_zero

theorem tripleBoundary_G_exponential (u v : ℝ) :
    tripleRetainedG (Real.exp u) (Real.exp v) =
      (1+v)*(u+v/2)*Real.exp (-(2*v)) +
      (1+u)*(v+u/2)*Real.exp (-(2*u)) := by
  rw [tripleBoundary_G_logarithms _ _ (Real.exp_pos _) (Real.exp_pos _),Real.log_exp,Real.log_exp]
  have hu := inverse_exp_square u
  have hv := inverse_exp_square v
  have heu : (Real.exp u)^2 ≠ 0 := by positivity
  have hev : (Real.exp v)^2 ≠ 0 := by positivity
  have h1 : 1/(Real.exp u)^2=Real.exp (-(2*u)) := (div_eq_iff heu).mpr (by nlinarith [hu])
  have h2 : 1/(Real.exp v)^2=Real.exp (-(2*v)) := (div_eq_iff hev).mpr (by nlinarith [hv])
  calc
    _ = (1+v)*(u+v/2)*(1/(Real.exp v)^2)+(1+u)*(v+u/2)*(1/(Real.exp u)^2) := by ring
    _ = _ := by rw [h1,h2]

theorem tripleBoundary_main_exponential (ω : ℝ → ℝ) (T u v : ℝ) :
    tripleRetainedMain ω T (Real.exp u) (Real.exp v) =
      Real.log T^3*Real.exp (-(2*(u+v))) +
      (Real.log T+tripleSmoothingMean ω)*
        ((1+v)*(u+v/2)*Real.exp (-(2*v))+
         (1+u)*(v+u/2)*Real.exp (-(2*u))) := by
  unfold tripleRetainedMain
  rw [tripleBoundary_G_exponential,← Real.exp_add]
  have h := inverse_exp_square (u+v)
  have he : 1/(Real.exp (u+v))^2 = Real.exp (-(2*(u+v))) :=
    (div_eq_iff (by positivity)).mpr (by nlinarith [h])
  rw [div_eq_mul_one_div,he]

theorem tripleBoundary_axis_main (ω : ℝ → ℝ) (T b r s : ℝ) :
    tripleRetainedMain ω T (Real.exp (b*r)) (Real.exp s) =
      Real.log T^3*Real.exp (-(2*(b*r+s))) +
      (Real.log T+tripleSmoothingMean ω)*
        ((1+s)*(b*r+s/2)*Real.exp (-(2*s))+
         (1+b*r)*(s+b*r/2)*Real.exp (-(2*(b*r)))) :=
  tripleBoundary_main_exponential ω T (b*r) s

theorem tripleBoundary_remainder_exact (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleQuadrantRemainder ω T X Y =
      (∑ e : TripleBudgetError, tripleBudgetError ω T X Y e) +
      (∑ w ∈ tripleBudgetRemainderWords, tripleBudgetWordError ω T X Y w) +
      ((tripleRetainedErrorD ω T X Y+tripleRetainedErrorJ ω T X Y-
        triplePrimeResonantMass X Y : ℝ):ℂ) := by
  rw [tripleQuadrantRemainder,tripleBudget_exact ω hω.smooth.continuous
    (tripleBudgetWeight_support ω hω) T X Y hT hX hY,tripleRetained_exact ω T X Y hX hY]
  push_cast
  ring

end
end HigherCorrelations
