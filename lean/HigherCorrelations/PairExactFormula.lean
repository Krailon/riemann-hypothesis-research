import HigherCorrelations.PairExactInterior
import HigherCorrelations.PairPrimeConvergence

/-! UNCONDITIONAL exact pair explicit formula, including X=1 by right continuity.
Zeros retain their actual real parts and are counted with analytic multiplicity.
No simplicity assumption, critical-line substitution, or endpoint half-weight occurs. -/
namespace HigherCorrelations
noncomputable section
open Complex Filter
open scoped Topology

theorem pairExact_endpoint (t : ℝ) :
    pairZeroSeries (1,t) = -pairPrimeSeries (1,t)-pairShiftCorrection (1,t)+
      pairPoleCorrection (1,t)+pairTrivialCorrection (1,t) := by
  have hp : Tendsto (fun X : ℝ => (X,t)) (𝓝[>] (1:ℝ))
      (𝓝[pairSeriesDomain] (1,t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.prodMk continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with X hX
    change 1 ≤ X
    exact le_of_lt hX
  have hz := (pairZeroSeries_continuous (1,t) (by simp [pairSeriesDomain])).tendsto.comp hp
  have hprime := (pairPrimeSeries_continuous (1,t) (by simp [pairSeriesDomain])).tendsto.comp hp
  have htriv := (pairTrivialCorrection_continuous (1,t) (by simp [pairSeriesDomain])).tendsto.comp hp
  have hshift : ContinuousAt (fun X : ℝ => pairShiftCorrection (X,t)) 1 := by
    unfold pairShiftCorrection
    apply ContinuousAt.mul
    · exact Complex.continuous_ofReal.continuousAt.inv₀ (by norm_num)
    · exact continuousAt_const
  have hpole : ContinuousAt (fun X : ℝ => pairPoleCorrection (X,t)) 1 := by
    unfold pairPoleCorrection
    dsimp only [Prod.fst,Prod.snd]
    apply ContinuousAt.div_const
    apply continuousAt_const.mul
    apply Complex.continuous_exp.continuousAt.comp
    apply ContinuousAt.mul
    · exact Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log (by norm_num))
    · exact continuousAt_const
  have hr := ((hprime.neg.sub (hshift.tendsto.mono_left nhdsWithin_le_nhds)).add
    (hpole.tendsto.mono_left nhdsWithin_le_nhds)).add htriv
  apply tendsto_nhds_unique hz
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with X hX
  exact (pairExact_interior X t hX).symm

/-- Exact project-normalized identity for every X≥1 and every real t. -/
theorem pairExact_formula (X t : ℝ) (hX : 1 ≤ X) :
    pairZeroSeries (X,t) = -pairPrimeSeries (X,t)-pairShiftCorrection (X,t)+
      pairPoleCorrection (X,t)+pairTrivialCorrection (X,t) := by
  rcases eq_or_lt_of_le hX with rfl|hX
  · exact pairExact_endpoint t
  · exact pairExact_interior X t hX

end
end HigherCorrelations
