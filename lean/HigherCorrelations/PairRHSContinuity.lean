import HigherCorrelations.PairRHSArchIntegrals
import HigherCorrelations.PairUniformFormula
import HigherCorrelations.PairMeanPrimeBridge
import Mathlib.Analysis.Complex.CauchyIntegral

/-! UNCONDITIONAL. Compact-interval continuity of the actual explicit-formula terms. -/
namespace HigherCorrelations
noncomputable section

theorem pairRHS_prime_continuous (X : ℝ) (hX : 1 ≤ X) :
    Continuous (fun t : ℝ => pairPrimeSeries (X,t)) := by
  have h := pairFrequencySum_continuous pairMeanPrimeFrequency
      (fun n => (pairMeanPrimeCoefficient X n:ℂ)) (pairMeanPrimeCoefficient_summable X hX)
  convert h using 1
  funext t
  exact pairMeanPrimeSeries_frequency X t

theorem pairRHS_remainder_continuous (j : PairRemainderKind) (X : ℝ) (hX : 1 ≤ X) :
    Continuous (pairRHSRemainder j X) := by
  cases j
  · change Continuous (fun t : ℝ => pairArchError (X,t))
    apply continuous_iff_continuousAt.mpr
    intro t
    have hz : (pairSpectralPoint t-1).re < 0 := by norm_num [pairSpectralPoint]
    have ha : AnalyticAt ℂ pairChi (pairSpectralPoint t-1) :=
      (show DifferentiableOn ℂ pairChi {z : ℂ | z.re < 0} from
        fun z hz => (pairChi_differentiable z hz).differentiableWithinAt).analyticAt
        ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz)
    have hc : ContinuousAt (fun u : ℝ => pairSpectralPoint u-1) t := by
      unfold pairSpectralPoint; fun_prop
    unfold pairArchError
    dsimp only [Prod.fst,Prod.snd]
    exact continuousAt_const.mul (((ha.deriv.continuousAt.comp (f := fun u : ℝ => pairSpectralPoint u-1) hc).neg.div
      (ha.continuousAt.comp (f := fun u : ℝ => pairSpectralPoint u-1) hc) (pairChi_ne_zero t)).sub
      (Complex.continuous_ofReal.continuousAt.comp
        ((continuous_abs.continuousAt.add_const 2).log (by positivity))))
  · change Continuous (fun t : ℝ => pairDSError (X,t))
    apply continuous_iff_continuousAt.mpr
    intro t
    have hz : 1 < (2-pairSpectralPoint t).re := by norm_num [pairSpectralPoint]
    have ha : AnalyticAt ℂ riemannZeta (2-pairSpectralPoint t) :=
      (show DifferentiableOn ℂ riemannZeta {z : ℂ | 1 < z.re} from fun z hz =>
        (differentiableAt_riemannZeta (by intro he; simp [he] at hz)).differentiableWithinAt).analyticAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    have hc : ContinuousAt (fun u : ℝ => 2-pairSpectralPoint u) t := by
      unfold pairSpectralPoint; fun_prop
    unfold pairDSError
    dsimp only [Prod.fst,Prod.snd]
    exact continuousAt_const.mul ((ha.deriv.continuousAt.comp (f := fun u : ℝ => 2-pairSpectralPoint u) hc).div
      (ha.continuousAt.comp (f := fun u : ℝ => 2-pairSpectralPoint u) hc) (riemannZeta_ne_zero_of_one_lt_re hz))
  · change Continuous (fun t : ℝ => pairPoleCorrection (X,t))
    unfold pairPoleCorrection
    dsimp only [Prod.fst,Prod.snd]
    apply Continuous.div
    · unfold pairSpectralPoint; fun_prop
    · unfold pairSpectralPoint; fun_prop
    · intro t
      have h := pairPole_denominator_lower t
      intro he
      rw [he,norm_zero] at h
      nlinarith [sq_nonneg t]
  · exact pairTrivialCorrection_continuous.comp_continuous
      (continuous_const.prodMk continuous_id) (fun t => hX)

theorem pairRHS_remainder_sum (X t : ℝ) :
    pairRHSRemainderSum X t = pairRHSRemainder .arch X t+pairRHSRemainder .ds X t+
      pairRHSRemainder .pole X t+pairRHSRemainder .trivial X t := by
  simp [pairRHSRemainderSum, Finset.univ, Fintype.elems, add_assoc]

theorem pairRHS_eq_zeroSeries (X t : ℝ) (hX : 1 ≤ X) (ht : 0 ≤ t) :
    pairRHS X t = pairZeroSeries (X,t) := by
  rw [pairUniform_formula X t hX,abs_of_nonneg ht]
  simp only [pairRHS,pairRHS_remainder_sum,pairRHSRemainder,pairRHSArch,
    Complex.ofReal_div,div_eq_mul_inv]
  push_cast
  ring

theorem pairRHSSquare_integrable (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => ‖pairRHS X t‖^2) MeasureTheory.volume 0 T := by
  have hp := (pairRHS_prime_continuous X hX).continuousOn (s := Set.Icc 0 T)
  have ha := pairRHSArch_continuous X T hT
  have hh : ContinuousOn (pairRHSRemainderSum X) (Set.Icc 0 T) :=
    continuousOn_finsetSum _ (fun j _ => (pairRHS_remainder_continuous j X hX).continuousOn)
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hT]
  exact ((hp.neg.add ha).add hh).norm.pow 2

theorem pairZeroMeanSquare_integrable (X T : ℝ) (hX : 1 ≤ X) :
    IntervalIntegrable (fun t : ℝ => ‖pairZeroSeries (X,t)‖^2) MeasureTheory.volume 0 T := by
  have hc : Continuous (fun t : ℝ => pairZeroSeries (X,t)) :=
    pairZeroSeries_continuous.comp_continuous (continuous_const.prodMk continuous_id) (fun t => hX)
  exact (hc.norm.pow 2).intervalIntegrable 0 T

theorem pairRHSSquare_eq_zeroMeanSquare (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSSquare X T = pairZeroMeanSquare X T := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hT] at ht
  dsimp only
  rw [pairRHS_eq_zeroSeries X t hX ht.1]

end
end HigherCorrelations
