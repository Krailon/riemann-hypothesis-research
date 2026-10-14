import HigherCorrelations.PairContourAlgebra
import HigherCorrelations.ZeroOccurrences
import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Helpers

/-! Residues for the exact pair formula. UNCONDITIONAL.
The zero residue carries the full analytic multiplicity. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem pairContour_residue_of_order (X t : ℝ) (z : ℂ) (m : ℤ)
    (hm : meromorphicOrderAt riemannZeta z = m)
    (hzp : z ≠ pairSpectralPoint t + 1) (hzm : z ≠ pairSpectralPoint t - 1) :
    residue (pairContourIntegrand X t) z = -(m:ℂ)*pairContourKernel X t z := by
  apply residue_eq_of_tendsto
  have hc : Tendsto (pairContourKernel X t) (𝓝[≠] z) (𝓝 (pairContourKernel X t z)) :=
    (pairContourKernel_continuousAt X t z hzp hzm).tendsto.mono_left nhdsWithin_le_nhds
  convert (tendsto_sub_mul_neg_zeta_logDeriv hm).mul hc using 1
  ext w
  simp only [pairContourIntegrand]
  ring

theorem pairContour_residue_zero (X t : ℝ) (i : ZeroOccurrence) :
    residue (pairContourIntegrand X t) (occurrenceValue i) =
      (zeroMultiplicity i.1 : ℂ)*pairZeroTerm i (X,t) := by
  have hm : meromorphicOrderAt riemannZeta (occurrenceValue i) =
      ((zeroMultiplicity i.1 : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt riemannZeta i.1.val = _
    rw [(stripZero_analytic i.1).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (stripZero_order_finite i.1)]
    rfl
  have hp : occurrenceValue i ≠ pairSpectralPoint t + 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, pairSpectralPoint_re, Complex.one_re] at hh
    have hi := i.1.property.2.2
    change (occurrenceValue i).re < 1 at hi
    linarith
  have hn : occurrenceValue i ≠ pairSpectralPoint t - 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, pairSpectralPoint_re, Complex.one_re] at hh
    have hi := i.1.property.2.1
    change 0 < (occurrenceValue i).re at hi
    linarith
  rw [pairContour_residue_of_order X t _ _ hm hp hn, pairContourKernel_zero]
  simp

theorem pairContour_residue_pole (X t : ℝ) :
    residue (pairContourIntegrand X t) 1 = -pairPoleCorrection (X,t) := by
  have hp : (1:ℂ) ≠ pairSpectralPoint t + 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, pairSpectralPoint_re, Complex.one_re] at hh
    norm_num at hh
  have hn : (1:ℂ) ≠ pairSpectralPoint t - 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, pairSpectralPoint_re, Complex.one_re] at hh
    norm_num at hh
  rw [pairContour_residue_of_order X t 1 (-1) meromorphicOrderAt_riemannZeta_one hp hn]
  simpa using pairContourKernel_pole X t

theorem pairKernel_plus_limit (X t : ℝ) (hX : 0 < X) :
    Tendsto (fun z => (z-(pairSpectralPoint t+1))*pairContourKernel X t z)
      (𝓝[≠] (pairSpectralPoint t+1)) (𝓝 (X:ℂ)) := by
  have heq : (fun z => (z-(pairSpectralPoint t+1))*pairContourKernel X t z)
      =ᶠ[𝓝[≠] (pairSpectralPoint t+1)]
      (fun z => 2*Complex.exp ((Real.log X:ℂ)*(z-pairSpectralPoint t)) /
        (z-(pairSpectralPoint t-1))) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hn : z-(pairSpectralPoint t+1) ≠ 0 := sub_ne_zero.mpr hz
    unfold pairContourKernel
    rw [pairContourKernel_denominator_factor]
    field_simp
  apply Tendsto.congr' heq.symm
  have hc : ContinuousAt (fun z : ℂ =>
      2*Complex.exp ((Real.log X:ℂ)*(z-pairSpectralPoint t)) /
        (z-(pairSpectralPoint t-1))) (pairSpectralPoint t+1) := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    have : pairSpectralPoint t+1-(pairSpectralPoint t-1) = (2:ℂ) := by ring
    rw [this]; norm_num
  have hl := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {pairSpectralPoint t+1}ᶜ))
  convert hl using 1
  rw [show pairSpectralPoint t+1-pairSpectralPoint t = (1:ℂ) by ring,
    show pairSpectralPoint t+1-(pairSpectralPoint t-1) = (2:ℂ) by ring]
  simp [← Complex.ofReal_exp, Real.exp_log hX]

theorem pairKernel_minus_limit (X t : ℝ) (hX : 0 < X) :
    Tendsto (fun z => (z-(pairSpectralPoint t-1))*pairContourKernel X t z)
      (𝓝[≠] (pairSpectralPoint t-1)) (𝓝 (-(X:ℂ)⁻¹)) := by
  have heq : (fun z => (z-(pairSpectralPoint t-1))*pairContourKernel X t z)
      =ᶠ[𝓝[≠] (pairSpectralPoint t-1)]
      (fun z => 2*Complex.exp ((Real.log X:ℂ)*(z-pairSpectralPoint t)) /
        (z-(pairSpectralPoint t+1))) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hn : z-(pairSpectralPoint t-1) ≠ 0 := sub_ne_zero.mpr hz
    unfold pairContourKernel
    rw [pairContourKernel_denominator_factor]
    field_simp
  apply Tendsto.congr' heq.symm
  have hc : ContinuousAt (fun z : ℂ =>
      2*Complex.exp ((Real.log X:ℂ)*(z-pairSpectralPoint t)) /
        (z-(pairSpectralPoint t+1))) (pairSpectralPoint t-1) := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    have : pairSpectralPoint t-1-(pairSpectralPoint t+1) = (-2:ℂ) := by ring
    rw [this]; norm_num
  have hl := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {pairSpectralPoint t-1}ᶜ))
  convert hl using 1
  rw [show pairSpectralPoint t-1-pairSpectralPoint t = (-1:ℂ) by ring,
    show pairSpectralPoint t-1-(pairSpectralPoint t+1) = (-2:ℂ) by ring]
  simp only [mul_neg_one, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hX]
  ring

theorem pairShift_zeta_ne_zero (t : ℝ) : riemannZeta (pairSpectralPoint t-1) ≠ 0 := by
  by_cases ht : t = 0
  · subst t
    convert Kadiri.riemannZeta_ne_zero_of_real_neg
      (σ := -(1/2)) (by norm_num) (by norm_num) using 1 <;> norm_num [pairSpectralPoint]
  · apply Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero
    · simp [pairSpectralPoint]; norm_num
    · simpa [pairSpectralPoint] using ht

private theorem zetaLogDeriv_continuousAt (z : ℂ) (hz : z ≠ 1)
    (hζ : riemannZeta z ≠ 0) :
    ContinuousAt (fun w => -deriv riemannZeta w / riemannZeta w) z := by
  have ha : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz
  exact ha.deriv.continuousAt.neg.div ha.continuousAt hζ

theorem pairContour_residue_plus (X t : ℝ) (hX : 0 < X) :
    residue (pairContourIntegrand X t) (pairSpectralPoint t+1) =
      -(X:ℂ)*(deriv riemannZeta (pairSpectralPoint t+1) /
        riemannZeta (pairSpectralPoint t+1)) := by
  have hz : pairSpectralPoint t+1 ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, pairSpectralPoint_re, Complex.one_re] at hh
    norm_num at hh
  have hn : riemannZeta (pairSpectralPoint t+1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num [pairSpectralPoint])
  have hc := (zetaLogDeriv_continuousAt _ hz hn).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {pairSpectralPoint t+1}ᶜ))
  apply residue_eq_of_tendsto
  convert hc.mul (pairKernel_plus_limit X t hX) using 1
  · ext z; unfold pairContourIntegrand; ring
  · ring

theorem pairContour_residue_minus (X t : ℝ) (hX : 0 < X) :
    residue (pairContourIntegrand X t) (pairSpectralPoint t-1) =
      pairShiftCorrection (X,t) := by
  have hz : pairSpectralPoint t-1 ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, pairSpectralPoint_re, Complex.one_re] at hh
    norm_num at hh
  have hc := (zetaLogDeriv_continuousAt _ hz (pairShift_zeta_ne_zero t)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {pairSpectralPoint t-1}ᶜ))
  apply residue_eq_of_tendsto
  convert hc.mul (pairKernel_minus_limit X t hX) using 1
  · ext z; unfold pairContourIntegrand; ring
  · unfold pairShiftCorrection; ring

end
end HigherCorrelations
