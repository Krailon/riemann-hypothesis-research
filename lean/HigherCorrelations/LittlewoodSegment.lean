import HigherCorrelations.LittlewoodDefinitions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! UNCONDITIONAL. Transported segment logarithms and finite integration by parts. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Set Filter Topology

private theorem segment_analytic (f : ℂ → ℂ) (z v : ℂ) (x : ℝ)
    (hf : AnalyticAt ℂ f (z+x*v)) (hn : f (z+x*v) ≠ 0) :
    AnalyticAt ℝ (fun t : ℝ => v * logDeriv f (z+t*v)) x := by
  have hp : AnalyticAt ℝ (fun t : ℝ => z+(t:ℂ)*v) x := analyticAt_const.add ((Complex.ofRealCLM.analyticAt x).mul analyticAt_const)
  have hq : AnalyticAt ℝ (fun s : ℂ => deriv f s / f s) (z+x*v) :=
    (hf.deriv.div hf hn).restrictScalars
  exact analyticAt_const.mul (hq.comp (f := fun t : ℝ => z+(t:ℂ)*v) hp)

private theorem analytic_measurable {Q : ℝ → ℂ} {x : ℝ} (h : AnalyticAt ℝ Q x) :
    StronglyMeasurableAtFilter Q (𝓝 x) volume :=
  ContinuousAt.stronglyMeasurableAtFilter (isOpen_analyticAt ℝ Q)
    (fun _ hh => hh.continuousAt) x h

theorem littlewoodSegmentLog_start (f : ℂ → ℂ) (z v : ℂ) (t₀ : ℝ) (k : ℂ) :
    littlewoodSegmentLog f z v t₀ k t₀ = k := by simp [littlewoodSegmentLog]

theorem littlewoodSegmentLog_deriv (f : ℂ → ℂ) (z v : ℂ) (a b t₀ t : ℝ) (k : ℂ)
    (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, AnalyticAt ℂ f (z+x*v))
    (hn : ∀ x ∈ Icc a b, f (z+x*v) ≠ 0) :
    HasDerivAt (littlewoodSegmentLog f z v t₀ k) (v * logDeriv f (z+t*v)) t := by
  have hc : ContinuousOn (fun x : ℝ => v * logDeriv f (z+x*v)) (Icc a b) :=
    fun x hx => (segment_analytic f z v x (hf x hx) (hn x hx)).continuousAt.continuousWithinAt
  have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc h₀ ht
  have hq := segment_analytic f z v t (hf t ht) (hn t ht)
  exact (intervalIntegral.integral_hasDerivAt_right
    ((hc.mono hsub).intervalIntegrable) (analytic_measurable hq) hq.continuousAt).const_add k

theorem littlewoodSegmentLog_exp (f : ℂ → ℂ) (z v : ℂ) (a b t₀ t : ℝ) (k : ℂ)
    (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, AnalyticAt ℂ f (z+x*v))
    (hn : ∀ x ∈ Icc a b, f (z+x*v) ≠ 0) (hk : exp k = f (z+t₀*v)) :
    exp (littlewoodSegmentLog f z v t₀ k t) = f (z+t*v) := by
  let L := littlewoodSegmentLog f z v t₀ k
  let G := fun x : ℝ => f (z+x*v) * exp (-L x)
  have hG : ∀ x ∈ Icc a b, HasDerivAt G 0 x := by
    intro x hx
    have hL := littlewoodSegmentLog_deriv f z v a b t₀ x k h₀ hx hf hn
    have hF : HasDerivAt (fun x : ℝ => f (z+x*v)) (deriv f (z+x*v)*v) x := by
      simpa using ((hf x hx).differentiableAt.hasDerivAt.comp (x:ℂ)
        (((hasDerivAt_id (x:ℂ)).mul_const v).const_add z)).comp_ofReal
    convert hF.mul hL.neg.cexp using 1
    dsimp [L]
    rw [logDeriv_apply]
    field_simp [hn x hx]
    <;> ring
  have hc : ContinuousOn G (Icc a b) := fun x hx => (hG x hx).continuousAt.continuousWithinAt
  have he := constant_of_has_deriv_right_zero hc (fun x hx => (hG x ⟨hx.1,hx.2.le⟩).hasDerivWithinAt)
  have hconst : G t = G t₀ := (he t ht).trans (he t₀ h₀).symm
  have hbase : G t₀ = 1 := by
    dsimp [G,L]
    rw [littlewoodSegmentLog_start, ← hk, ← exp_add]
    simp
  rw [hbase] at hconst
  dsimp [G] at hconst
  have hh := congrArg (fun w : ℂ => w * exp (L t)) hconst
  simpa [mul_assoc, ← exp_add] using hh.symm

theorem littlewoodSegmentLog_re (f : ℂ → ℂ) (z v : ℂ) (a b t₀ t : ℝ) (k : ℂ)
    (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, AnalyticAt ℂ f (z+x*v))
    (hn : ∀ x ∈ Icc a b, f (z+x*v) ≠ 0) (hk : exp k = f (z+t₀*v)) :
    (littlewoodSegmentLog f z v t₀ k t).re = Real.log ‖f (z+t*v)‖ := by
  rw [← littlewoodSegmentLog_exp f z v a b t₀ t k h₀ ht hf hn hk, norm_exp, Real.log_exp]

theorem littlewood_affine_integral (L Q : ℝ → ℂ) (a b : ℝ) (w₀ w₁ : ℂ)
    (hab : a ≤ b) (hL : ∀ x ∈ Icc a b, HasDerivAt L (Q x) x)
    (hQ : ContinuousOn Q (Icc a b)) :
    (∫ x in a..b, (w₀+x*w₁)*Q x) =
      (w₀+b*w₁)*L b-(w₀+a*w₁)*L a-w₁*(∫ x in a..b, L x) := by
  have hcL : ContinuousOn L (Icc a b) := fun x hx => (hL x hx).continuousAt.continuousWithinAt
  have hcW : ContinuousOn (fun x : ℝ => w₀+x*w₁) (Icc a b) := by fun_prop
  have hiL : IntervalIntegrable (fun x => w₁*L x) volume a b := (hcL.const_mul w₁).intervalIntegrable_of_Icc hab
  have hiQ : IntervalIntegrable (fun x => (w₀+x*w₁)*Q x) volume a b := (hcW.mul hQ).intervalIntegrable_of_Icc hab
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (hx : x ∈ uIcc a b) =>
      ((((hasDerivAt_id (x:ℂ)).mul_const w₁).const_add w₀).comp_ofReal.mul
        (hL x (by simpa [uIcc_of_le hab] using hx)))) (by simpa using hiL.add hiQ)
  simp only [one_mul, id_eq, Pi.mul_apply] at hh
  rw [intervalIntegral.integral_add hiL hiQ, intervalIntegral.integral_const_mul] at hh
  linear_combination hh

theorem littlewood_integral_re (F : ℝ → ℂ) (a b : ℝ) (hF : IntervalIntegrable F volume a b) :
    (∫ x in a..b, F x).re = ∫ x in a..b, (F x).re := by
  exact (Complex.reCLM.intervalIntegral_comp_comm hF).symm

theorem littlewood_integral_im (F : ℝ → ℂ) (a b : ℝ) (hF : IntervalIntegrable F volume a b) :
    (∫ x in a..b, F x).im = ∫ x in a..b, (F x).im := by
  exact (Complex.imCLM.intervalIntegral_comp_comm hF).symm

end
end HigherCorrelations
