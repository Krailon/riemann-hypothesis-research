import HigherCorrelations.ApproximateFunctionalHankelRay
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Analytic.Uniqueness

/-! UNCONDITIONAL analytic continuation of the fixed-radius Hankel identity.
This is separate from the saddle deformation and uniform AFE remainder. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology

theorem afe_compact_exp_integral_entire (w A : ℝ → ℂ) (hw : Continuous w)
    (hA : Continuous A) (a b : ℝ) :
    Differentiable ℂ (fun s : ℂ => ∫ θ : ℝ in a..b, A θ * exp (s*w θ)) := by
  intro s₀
  let F (s : ℂ) (θ : ℝ) := A θ * exp (s*w θ)
  let D (s : ℂ) (θ : ℝ) := A θ * exp (s*w θ) * w θ
  have hdiff (s : ℂ) (θ : ℝ) : HasDerivAt (fun s => F s θ) (D s θ) s := by
    convert (((hasDerivAt_id s).mul_const (w θ)).cexp).const_mul (A θ) using 1 <;>
      simp [F, D, mul_assoc, mul_comm, mul_left_comm]
  have hcF (s : ℂ) : Continuous (F s) := by dsimp [F]; fun_prop
  have hcD : Continuous (fun p : ℂ × ℝ => D p.1 p.2) := by dsimp [D]; fun_prop
  obtain ⟨M, hM⟩ := ((isCompact_closedBall s₀ 1).prod isCompact_uIcc).exists_bound_of_continuousOn
    hcD.continuousOn
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (F := F) (F' := D) (bound := fun _ => M)
    (Metric.ball_mem_nhds s₀ (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall (fun s => (hcF s).aestronglyMeasurable))
    (hcF s₀ |>.intervalIntegrable a b)
    ((hcD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (ae_of_all _ (fun θ hθ s hs => hM (s,θ)
      ⟨Metric.ball_subset_closedBall hs, uIoc_subset_uIcc hθ⟩))
    (intervalIntegrable_const) (ae_of_all _ (fun θ _ s _ => hdiff s θ))
  exact h.2.differentiableAt

theorem afeHankel_circle_differentiable (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    Differentiable ℂ (fun s : ℂ => ∮ z in C(0,r), afeHankelKernel s m z) := by
  let w (θ : ℝ) : ℂ := (Real.log r:ℂ)+(θ:ℂ)*I
  let A (θ : ℝ) : ℂ := exp (-(m:ℂ)*exp (w θ))/(exp (exp (w θ))-1)
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hd (θ : ℝ) : exp (exp (w θ))-1 ≠ 0 := by
    have hn : ‖exp (w θ)‖ = r := by
      rw [norm_exp]; simp [w, Real.exp_log hr]
    have h := afe_exp_small_denominator (exp (w θ)) (by rw [hn]; exact hr')
    intro he
    rw [he, norm_zero, hn] at h
    linarith
  have hA : Continuous A := by
    dsimp only [A]
    exact (by fun_prop : Continuous (fun θ => exp (-(m:ℂ)*exp (w θ)))).div
      (by fun_prop) hd
  have h := (afe_compact_exp_integral_entire w A hw hA 0 (2*Real.pi)).const_mul I
  have he : (fun s : ℂ => ∮ z in C(0,r), afeHankelKernel s m z) =
      fun s : ℂ => I * ∫ θ : ℝ in 0..2*Real.pi, A θ*exp (s*w θ) := by
    funext s
    rw [afeHankel_circle_lift s m r hr]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp [A, w, afeHankelLift]
    ring
  rw [he]
  exact h

theorem afePolynomial_differentiable (x : ℝ) :
    Differentiable ℂ (fun s : ℂ => afePolynomial s x) := by
  unfold afePolynomial
  apply Differentiable.fun_sum
  intro n hn
  have hn0 : (n:ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)
  exact differentiable_neg.const_cpow (Or.inl hn0)

theorem afeHankelPrefactor_differentiable (s : ℂ) (hs : s.im ≠ 0) :
    DifferentiableAt ℂ afeHankelPrefactor s := by
  have hg : DifferentiableAt ℂ (fun z : ℂ => Gamma (1-z)) s := by
    apply (differentiableAt_Gamma (1-s) ?_).comp s (differentiableAt_id.const_sub 1)
    intro n he
    apply hs
    have h := congrArg Complex.im he
    simpa using h
  unfold afeHankelPrefactor
  exact ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => exp (-(Real.pi:ℂ)*z*I)) s).mul hg).div_const _

theorem afeHankel_initial_identity_on (U : Set ℂ) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hnonreal : ∀ s ∈ U, s.im ≠ 0)
    (a : ℂ) (ha : a ∈ U) (ha' : 1 < a.re)
    (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    ∀ s ∈ U, riemannZeta s - afePolynomial s m =
      afeHankelPrefactor s * ((∮ z in C(0,r), afeHankelKernel s m z) +
        (exp (2*(Real.pi:ℂ)*s*I)-1) *
          ∫ u : ℝ in Ioi r,
            (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by
  let F (s : ℂ) := riemannZeta s - afePolynomial s m
  let G (s : ℂ) := afeHankelPrefactor s * ((∮ z in C(0,r), afeHankelKernel s m z) +
        (exp (2*(Real.pi:ℂ)*s*I)-1) *
          ∫ u : ℝ in Ioi r,
            (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1))
  have hf : DifferentiableOn ℂ F U := by
    intro s hs
    have hs1 : s ≠ 1 := by intro he; exact hnonreal s hs (by rw [he]; rfl)
    exact ((differentiableAt_riemannZeta hs1).sub
      (afePolynomial_differentiable m s)).differentiableWithinAt
  have hg : DifferentiableOn ℂ G U := by
    intro s hs
    have hc := afeHankel_circle_differentiable m r hr hr' s
    have hl := afeHankel_ray_differentiable m r hr s
    have he : DifferentiableAt ℂ (fun s : ℂ => exp (2*(Real.pi:ℂ)*s*I)-1) s := by fun_prop
    exact ((afeHankelPrefactor_differentiable s (hnonreal s hs)).mul
      (hc.add (he.mul hl))).differentiableWithinAt
  have heq : F =ᶠ[𝓝 a] G := by
    filter_upwards [hU.mem_nhds ha, continuous_re.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds ha')] with s hs hs'
    exact afeHankel_initial_identity s hs' (hnonreal s hs) m r hr hr'
  exact (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hU) hconn ha heq

theorem afeHankel_identity_nonreal (s : ℂ) (hs : s.im ≠ 0)
    (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    riemannZeta s - afePolynomial s m =
      afeHankelPrefactor s * ((∮ z in C(0,r), afeHankelKernel s m z) +
        (exp (2*(Real.pi:ℂ)*s*I)-1) *
          ∫ u : ℝ in Ioi r,
            (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by
  rcases lt_or_gt_of_ne hs with ht | ht
  · exact afeHankel_initial_identity_on {z : ℂ | z.im < 0}
      (isOpen_lt continuous_im continuous_const) (convex_halfSpace_im_lt 0).isPreconnected
      (fun z hz => ne_of_lt hz) (2+(s.im:ℂ)*I) (by simpa using ht) (by norm_num)
      m r hr hr' s ht
  · exact afeHankel_initial_identity_on {z : ℂ | 0 < z.im}
      (isOpen_lt continuous_const continuous_im) (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => ne_of_gt hz) (2+(s.im:ℂ)*I) (by simpa using ht) (by norm_num)
      m r hr hr' s ht

theorem afeHankel_identity_cutoff (s : ℂ) (hs : s.im ≠ 0)
    (x r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    riemannZeta s - afePolynomial s x =
      afeHankelPrefactor s * ((∮ z in C(0,r), afeHankelKernel s ⌊x⌋₊ z) +
        (exp (2*(Real.pi:ℂ)*s*I)-1) *
          ∫ u : ℝ in Ioi r,
            (u:ℂ)^(s-1)*exp (-((⌊x⌋₊:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by
  simpa only [afePolynomial, Nat.floor_natCast] using
    afeHankel_identity_nonreal s hs ⌊x⌋₊ r hr hr'

theorem afeHankel_residue_sum (s : ℂ) (m N : ℕ) :
    afeHankelPrefactor s * (2*(Real.pi:ℂ)*I) *
      (∑ k ∈ Finset.Icc 1 N,
        (residue (afeHankelKernel s m) ((2*Real.pi*k:ℝ)*I) +
         residue (afeHankelKernel s m) (-((2*Real.pi*k:ℝ)*I)))) =
      -pairChi s * afePolynomial (1-s) N := by
  rw [afePolynomial_nat]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [afeHankelKernel_residue_pair s m k (by have := (Finset.mem_Icc.mp hk).1; omega)]
  congr 2
  ring

end
end HigherCorrelations
