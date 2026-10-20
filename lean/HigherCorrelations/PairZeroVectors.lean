import HigherCorrelations.PairZeroDefinitions
import HigherCorrelations.PairZeroConvergence

/-! UNCONDITIONAL phase bridge. The full sum is absolutely convergent before
its scalar phase is removed. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairZeroVector_phase (i : ZeroOccurrence) (X t : ℝ) :
    pairZeroTerm i (X,t) = 2*Complex.exp (-Complex.I*t*Real.log X)*pairZeroVector i X t := by
  unfold pairZeroTerm pairZeroVector scalarKernel
  dsimp only
  rw [div_eq_mul_inv]
  have he : (Real.log X : ℂ)*((occurrenceDisplacement i:ℂ)+Complex.I*(occurrenceOrdinate i-t)) =
      -Complex.I*t*Real.log X+(Real.log X : ℂ)*
        ((occurrenceDisplacement i:ℂ)+Complex.I*occurrenceOrdinate i) := by push_cast; ring
  rw [he,Complex.exp_add]
  ring

theorem pairZero_phase_norm (X t : ℝ) : ‖Complex.exp (-Complex.I*t*Real.log X)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem pairZeroVector_summable (X t : ℝ) (hX : 1 ≤ X) :
    Summable (fun i => ‖pairZeroVector i X t‖) := by
  have h := (pairZeroTerm_summable X t hX).div_const 2
  simpa only [pairZeroVector_phase,norm_mul,pairZero_phase_norm,mul_one,
    Complex.norm_ofNat, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using h

theorem pairZeroFullVector_phase (X t : ℝ) (hX : 1 ≤ X) :
    pairZeroSeries (X,t) = 2*Complex.exp (-Complex.I*t*Real.log X)*pairZeroFullVector X t := by
  unfold pairZeroSeries pairZeroFullVector
  simp_rw [pairZeroVector_phase]
  exact tsum_mul_left

theorem pairZeroFullVector_eq (X t : ℝ) (hX : 1 ≤ X) :
    pairZeroFullVector X t = (2*Complex.exp (-Complex.I*t*Real.log X))⁻¹*pairZeroSeries (X,t) := by
  rw [pairZeroFullVector_phase X t hX]
  field_simp

theorem pairZeroVector_continuous (i : ZeroOccurrence) (X : ℝ) :
    Continuous (pairZeroVector i X) := by
  unfold pairZeroVector
  exact continuous_const.mul ((scalarKernel_continuous _
    (by linarith [pair_occurrence_displacement i])).comp (continuous_id.sub continuous_const))

theorem pairZeroFullVector_continuous (X : ℝ) (hX : 1 ≤ X) :
    Continuous (pairZeroFullVector X) := by
  have h := pairZeroSeries_continuous.comp_continuous
    (continuous_const.prodMk continuous_id) (fun t => hX)
  rw [show pairZeroFullVector X = (fun t : ℝ => (2*Complex.exp (-Complex.I*t*Real.log X))⁻¹*pairZeroSeries (X,t)) from
    funext (fun t => pairZeroFullVector_eq X t hX)]
  exact (Continuous.inv₀ (by fun_prop) (fun t => mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))).mul h

theorem pairZeroCutoffVector_continuous (X Z : ℝ) :
    Continuous (pairZeroCutoffVector X Z) :=
  continuous_finsetSum _ (fun i _ => pairZeroVector_continuous i X)

theorem pairZeroWindowVector_continuous (X T : ℝ) :
    Continuous (pairZeroWindowVector X T) :=
  continuous_finsetSum _ (fun i _ => pairZeroVector_continuous i X)

theorem pairZeroMeanSquare_eq_full (X T : ℝ) (hX : 1 ≤ X) :
    pairZeroMeanSquare X T = 4*∫ t in (0:ℝ)..T, ‖pairZeroFullVector X t‖^2 := by
  unfold pairZeroMeanSquare
  simp_rw [pairZeroFullVector_phase X _ hX,norm_mul,pairZero_phase_norm]
  norm_num only [Complex.norm_ofNat,mul_one]
  simp_rw [mul_pow]
  norm_num only
  exact intervalIntegral.integral_const_mul _ _

end
end HigherCorrelations
