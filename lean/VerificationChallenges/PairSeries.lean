import HigherCorrelations.PairSeriesDefinitions
import HigherCorrelations.UniformHeightDefinitions
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Definition-only specifications. Intentional unfinished challenge proofs;
solution modules never import this file. Assumptions: UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem pairSeriesRectangle_nhds (p : ℝ × ℝ) :
    pairSeriesRectangle (p.1+1) (|p.2|+1) ∈ 𝓝[pairSeriesDomain] p := by sorry

theorem pairSeries_locallyUniform {ι : Type*} {l : Filter ι}
    {F : ι → (ℝ × ℝ) → ℂ} {f : (ℝ × ℝ) → ℂ}
    (h : ∀ B H : ℝ, 1≤B → TendstoUniformlyOn F f l (pairSeriesRectangle B H)) :
    TendstoLocallyUniformlyOn F f l pairSeriesDomain := by sorry

theorem pair_occurrence_displacement (i : ZeroOccurrence) : |occurrenceDisplacement i| ≤ 1/2 := by sorry

theorem pair_denominator_lower (v d : ℝ) (hd : |d| ≤ 1/2) :
    (3/4 : ℝ)*(1+v^2) ≤ ‖1+((v:ℂ)+Complex.I*d)^2‖ := by sorry

theorem pairZeroTerm_bound (i : ZeroOccurrence) (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroTerm i (X,t)‖ ≤ (8/3 : ℝ)*Real.sqrt X*ordinateKernel (t-occurrenceOrdinate i) := by sorry

theorem pairZeroTerm_summable (X t : ℝ) (hX : 1 ≤ X) :
    Summable (fun i => ‖pairZeroTerm i (X,t)‖) := by sorry

theorem pairZeroTail_bound : ∃ C : ℝ, 0<C ∧ ∀ X t U : ℝ, 1≤X → 2*(|t|+2)≤U →
    pairZeroTail X t U ≤ C*Real.sqrt X*Real.log U/U := by sorry

theorem pair_kernel_rectangle (t g H : ℝ) (ht : |t| ≤ H) :
    ordinateKernel (t-g) ≤ (2+2*H^2)*ordinateKernel g := by sorry

theorem pairZero_rectangle_majorant (B H : ℝ) (hB : 1 ≤ B) :
    ∃ M : ZeroOccurrence → ℝ, Summable M ∧
      ∀ i p, p ∈ pairSeriesRectangle B H → ‖pairZeroTerm i p‖ ≤ M i := by sorry

theorem pairZero_uniform_rectangle (B H : ℝ) (hB : 1≤B) :
    TendstoUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, pairZeroTerm i p)
      pairZeroSeries atTop (pairSeriesRectangle B H) := by sorry

theorem pairZeroTerm_continuous (i : ZeroOccurrence) : ContinuousOn (pairZeroTerm i) pairSeriesDomain := by sorry

theorem pairZero_locallyUniform :
    TendstoLocallyUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, pairZeroTerm i p)
      pairZeroSeries atTop pairSeriesDomain := by sorry

theorem pairZeroSeries_continuous : ContinuousOn pairZeroSeries pairSeriesDomain := by sorry

theorem pair_occurrenceCutoff_tendsto : Tendsto occurrenceCutoff atTop atTop := by sorry

theorem pairZero_cutoff_uniform (B H : ℝ) (hB : 1≤B) :
    TendstoUniformlyOn (fun U : ℝ => fun p => ∑ i ∈ occurrenceCutoff U, pairZeroTerm i p)
      pairZeroSeries atTop (pairSeriesRectangle B H) := by sorry

theorem pairZero_cutoff_locallyUniform :
    TendstoLocallyUniformlyOn (fun U : ℝ => fun p => ∑ i ∈ occurrenceCutoff U, pairZeroTerm i p)
      pairZeroSeries atTop pairSeriesDomain := by sorry

theorem pairZero_cutoff_remainder (X t U : ℝ) (hX : 1≤X) :
    ‖pairZeroSeries (X,t) - ∑ i ∈ occurrenceCutoff U, pairZeroTerm i (X,t)‖ ≤ pairZeroTail X t U := by sorry

theorem pairPrimeTerm_summable (X t : ℝ) (hX : 1≤X) :
    Summable (fun n => ‖pairPrimeTerm n (X,t)‖) := by sorry

theorem pairPrime_uniform_rectangle (B H : ℝ) (_hB : 1≤B) :
    TendstoUniformlyOn (fun N : ℕ => fun p => ∑ n ∈ Finset.range N, pairPrimeTerm n p)
      pairPrimeSeries atTop (pairSeriesRectangle B H) := by sorry

theorem pairPrime_locallyUniform :
    TendstoLocallyUniformlyOn (fun N : ℕ => fun p => ∑ n ∈ Finset.range N, pairPrimeTerm n p)
      pairPrimeSeries atTop pairSeriesDomain := by sorry

theorem pairPrimeTerm_continuous (n : ℕ) : ContinuousOn (pairPrimeTerm n) pairSeriesDomain := by sorry

theorem pairPrimeSeries_continuous : ContinuousOn pairPrimeSeries pairSeriesDomain := by sorry

theorem pairPrimeTerm_one (p : ℝ × ℝ) : pairPrimeTerm 0 p = 0 := by sorry

theorem pairSeries_convergence :
    (∀ X t : ℝ, 1≤X → Summable (fun i => ‖pairZeroTerm i (X,t)‖) ∧
      Summable (fun n => ‖pairPrimeTerm n (X,t)‖)) ∧
    ContinuousOn pairZeroSeries pairSeriesDomain ∧
    ContinuousOn pairPrimeSeries pairSeriesDomain ∧
    (∃ C : ℝ, 0<C ∧ ∀ X t U : ℝ, 1≤X → 2*(|t|+2)≤U →
      pairZeroTail X t U ≤ C*Real.sqrt X*Real.log U/U) := by sorry

theorem pairZero_cutoff_error : ∃ C : ℝ, 0<C ∧ ∀ X t U : ℝ, 1≤X → 2*(|t|+2)≤U →
    ‖pairZeroSeries (X,t) - ∑ i ∈ occurrenceCutoff U, pairZeroTerm i (X,t)‖ ≤
      C*Real.sqrt X*Real.log U/U := by sorry

theorem pairPrimeTerm_at_knot (n : ℕ) (t : ℝ) :
    pairPrimeTerm n (n+1,t) = (ArithmeticFunction.vonMangoldt (n+1) : ℂ) *
      Complex.exp ((Real.log (n+1 : ℝ) : ℂ)*(-(1/2 : ℂ)-Complex.I*t)) := by sorry

theorem pairZeroTerm_at_one (i : ZeroOccurrence) (t : ℝ) :
    pairZeroTerm i (1,t) = 2 / (1+((t-occurrenceOrdinate i : ℝ)+Complex.I*occurrenceDisplacement i)^2) := by sorry

end
end HigherCorrelations
