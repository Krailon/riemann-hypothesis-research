import HigherCorrelations.PairBoundaryLimits
import HigherCorrelations.PairResidueRegrouping
import HigherCorrelations.PairPrimeIdentity
import HigherCorrelations.PairZeroConvergence
import HigherCorrelations.PairTrivialCorrection

/-! UNCONDITIONAL exact pair formula for X > 1. The contour limit order is
height to infinity at fixed left shift, then left shift to infinity. -/
namespace HigherCorrelations
noncomputable section
open Complex Filter
open scoped Topology

theorem pairExact_fixedLeft (X t : ℝ) (M : ℕ) (hX : 1 ≤ X) :
    pairRightIntegral (X,t)-pairLeftIntegral X t M =
      pairZeroSeries (X,t)-pairPoleCorrection (X,t)-
      (∑ n ∈ Finset.range M, pairTrivialTerm n (X,t))-
      (X:ℂ)*(deriv riemannZeta (pairSpectralPoint t+1)/riemannZeta (pairSpectralPoint t+1))+
      pairShiftCorrection (X,t) := by
  obtain ⟨C,U,hC,hU,hUt,hgap⟩ := pairGoodHeight_sequence
  have hl := pairRectangle_height_tendsto X t C M hX hC U hU hUt hgap
  have hz := ((pairZeroTerm_summable X t hX).of_norm.hasSum).comp
    (pair_occurrenceCutoff_tendsto.comp hUt)
  have hr := (((hz.sub_const (pairPoleCorrection (X,t))).sub_const
    (∑ n ∈ Finset.range M, pairTrivialTerm n (X,t))).sub_const
    ((X:ℂ)*(deriv riemannZeta (pairSpectralPoint t+1)/riemannZeta (pairSpectralPoint t+1)))).add_const
    (pairShiftCorrection (X,t))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [hUt.eventually_gt_atTop (|t|+1)] with n hn
  have hUpos : 0 < U n := by have := abs_nonneg t; linarith
  have hε : 0 < 1/(C*Real.log ((n:ℝ)+6)) := by
    have hlog : 0 < Real.log ((n:ℝ)+6) := Real.log_pos (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
    positivity
  rw [pairContour_finite_rectangle X t (U n) (1/(C*Real.log ((n:ℝ)+6))) M
    (by linarith) hUpos (by linarith) hε (fun i => (hgap n i).1),
    pairContour_candidate_residue_sum X t (U n) M (by linarith)]
  rfl

theorem pairExact_interior (X t : ℝ) (hX : 1 < X) :
    pairZeroSeries (X,t) = -pairPrimeSeries (X,t)-pairShiftCorrection (X,t)+
      pairPoleCorrection (X,t)+pairTrivialCorrection (X,t) := by
  have hl := (tendsto_const_nhds (x := pairRightIntegral (X,t))).sub (pairLeftIntegral_tendsto X t hX)
  have ht := (pairTrivialTerm_summable (X,t) hX.le).of_norm.hasSum.tendsto_sum_nat
  have hr := (((tendsto_const_nhds (x := pairZeroSeries (X,t)-pairPoleCorrection (X,t))).sub ht).sub_const
    ((X:ℂ)*(deriv riemannZeta (pairSpectralPoint t+1)/riemannZeta (pairSpectralPoint t+1)))).add_const
    (pairShiftCorrection (X,t))
  have he : pairRightIntegral (X,t)-0 =
      pairZeroSeries (X,t)-pairPoleCorrection (X,t)-pairTrivialCorrection (X,t)-
      (X:ℂ)*(deriv riemannZeta (pairSpectralPoint t+1)/riemannZeta (pairSpectralPoint t+1))+
      pairShiftCorrection (X,t) :=
    tendsto_nhds_unique hl (hr.congr' (Filter.Eventually.of_forall
      (fun M => (pairExact_fixedLeft X t M hX.le).symm)))
  have hp := pairRightIntegral_prime_identity X t hX.le
  linear_combination hp - he

end
end HigherCorrelations
