import HigherCorrelations.PairSeriesDefinitions
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! UNCONDITIONAL rectangle-to-local-uniform bridge, including the closed X=1 edge. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem pairSeriesRectangle_nhds (p : ℝ × ℝ) :
    pairSeriesRectangle (p.1+1) (|p.2|+1) ∈ 𝓝[pairSeriesDomain] p := by
  have hB : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 < p.1+1 :=
    (continuous_fst.tendsto p).eventually (gt_mem_nhds (by linarith))
  have hH : ∀ᶠ q : ℝ × ℝ in 𝓝 p, |q.2| < |p.2|+1 :=
    (continuous_snd.abs.tendsto p).eventually (gt_mem_nhds (by linarith))
  filter_upwards [nhdsWithin_le_nhds hB, nhdsWithin_le_nhds hH, self_mem_nhdsWithin] with q hq hr hs
  exact ⟨hs,hq.le,hr.le⟩

theorem pairSeries_locallyUniform {ι : Type*} {l : Filter ι}
    {F : ι → (ℝ × ℝ) → ℂ} {f : (ℝ × ℝ) → ℂ}
    (h : ∀ B H : ℝ, 1≤B → TendstoUniformlyOn F f l (pairSeriesRectangle B H)) :
    TendstoLocallyUniformlyOn F f l pairSeriesDomain := by
  intro u hu p hp
  exact ⟨pairSeriesRectangle (p.1+1) (|p.2|+1), pairSeriesRectangle_nhds p,
    h _ _ (by have : 1≤p.1 := hp; linarith) u hu⟩

end
end HigherCorrelations
