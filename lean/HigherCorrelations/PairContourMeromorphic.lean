import HigherCorrelations.PairContourResidues
import Mathlib.Analysis.Meromorphic.Divisor

/-! UNCONDITIONAL meromorphy and simple-pole control for the pair contour. -/
namespace HigherCorrelations
noncomputable section
open Complex Filter
open scoped Topology

theorem pairContourKernel_meromorphic (X t : ℝ) : Meromorphic (pairContourKernel X t) := by
  intro z
  apply MeromorphicAt.div
  · exact (by fun_prop : AnalyticAt ℂ
      (fun w : ℂ => 2*Complex.exp ((Real.log X:ℂ)*(w-pairSpectralPoint t))) z).meromorphicAt
  · exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (w-pairSpectralPoint t)^2-1) z).meromorphicAt

theorem pairContourIntegrand_meromorphic (X t : ℝ) : Meromorphic (pairContourIntegrand X t) := by
  intro z
  exact ((meromorphicAt_riemannZeta z).deriv.neg.div (meromorphicAt_riemannZeta z)).mul
    (pairContourKernel_meromorphic X t z)

theorem pairContourIntegrand_analyticAt (X t : ℝ) (z : ℂ)
    (hz : z ≠ 1) (hζ : riemannZeta z ≠ 0)
    (hp : z ≠ pairSpectralPoint t+1) (hn : z ≠ pairSpectralPoint t-1) :
    AnalyticAt ℂ (pairContourIntegrand X t) z := by
  have ha := analyticOn_riemannZeta z hz
  apply (ha.deriv.neg.div ha hζ).mul
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  rw [pairContourKernel_denominator_factor]
  exact mul_ne_zero (sub_ne_zero.mpr hp) (sub_ne_zero.mpr hn)

private theorem simple_order_of_limit {f : ℂ → ℂ} {z c : ℂ} (hf : MeromorphicAt f z)
    (hl : Tendsto (fun w => (w-z)*f w) (𝓝[≠] z) (𝓝 c)) :
    ((-1:ℤ):WithTop ℤ) ≤ meromorphicOrderAt f z := by
  have hm : MeromorphicAt (fun w => (w-z)*f w) z :=
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w-z) z).meromorphicAt.mul hf
  have ho := (tendsto_nhds_iff_meromorphicOrderAt_nonneg hm).mp ⟨c,hl⟩
  change 0 ≤ meromorphicOrderAt ((fun w : ℂ => w-z)*f) z at ho
  rw [meromorphicOrderAt_mul (by fun_prop) hf, meromorphicOrderAt_id_sub_const] at ho
  exact (WithTop.add_le_add_iff_left (show (1:WithTop ℤ) ≠ ⊤ by simp)).mp (by simpa using ho)

/-- No coincident kernel/zeta poles: the two kernel poles lie on Re=3/2,-1/2. -/
theorem pairContour_simple_poles (X t : ℝ) (hX : 0 < X) :
    HasSimplePolesOn (pairContourIntegrand X t) Set.univ := by
  intro z _
  suffices ∃ c : ℂ, Tendsto (fun w => (w-z)*pairContourIntegrand X t w) (𝓝[≠] z) (𝓝 c) by
    obtain ⟨c,hc⟩ := this
    exact simple_order_of_limit (pairContourIntegrand_meromorphic X t z) hc
  by_cases hp : z = pairSpectralPoint t+1
  · subst z
    have hz : pairSpectralPoint t+1 ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      norm_num [pairSpectralPoint] at hr
    have ha := analyticOn_riemannZeta _ hz
    have hζ := riemannZeta_ne_zero_of_one_le_re (s := pairSpectralPoint t+1)
      (by norm_num [pairSpectralPoint])
    have hc := (ha.deriv.continuousAt.neg.div ha.continuousAt hζ).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {pairSpectralPoint t+1}ᶜ))
    refine ⟨(-deriv riemannZeta (pairSpectralPoint t+1) / riemannZeta (pairSpectralPoint t+1))*(X:ℂ),?_⟩
    convert hc.mul (pairKernel_plus_limit X t hX) using 1
    ext w; simp only [pairContourIntegrand, Pi.div_apply, Pi.neg_apply]; ring
  by_cases hn : z = pairSpectralPoint t-1
  · subst z
    have hz : pairSpectralPoint t-1 ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      norm_num [pairSpectralPoint] at hr
    have ha := analyticOn_riemannZeta _ hz
    have hc := (ha.deriv.continuousAt.neg.div ha.continuousAt (pairShift_zeta_ne_zero t)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {pairSpectralPoint t-1}ᶜ))
    refine ⟨(-deriv riemannZeta (pairSpectralPoint t-1) / riemannZeta (pairSpectralPoint t-1))*(-(X:ℂ)⁻¹),?_⟩
    convert hc.mul (pairKernel_minus_limit X t hX) using 1
    ext w; simp only [pairContourIntegrand, Pi.div_apply, Pi.neg_apply]; ring
  obtain ⟨m,hm⟩ := WithTop.ne_top_iff_exists.mp (meromorphicOrderAt_riemannZeta_ne_top z)
  have hc := (pairContourKernel_continuousAt X t z hp hn).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z}ᶜ))
  refine ⟨-(m:ℂ)*pairContourKernel X t z,?_⟩
  convert (tendsto_sub_mul_neg_zeta_logDeriv hm.symm).mul hc using 1
  ext w; simp only [pairContourIntegrand, Pi.div_apply, Pi.neg_apply]; ring

end
end HigherCorrelations
