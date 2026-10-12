import HigherCorrelations.ProfilePoleAlgebra

/-! UNCONDITIONAL identification of the absolutely integrable profile, including
coincident centers. The simple poles are used only on finite intervals. -/
namespace HigherCorrelations
noncomputable section
set_option maxHeartbeats 800000
open Filter MeasureTheory
open scoped Topology

theorem integralProfile_eq_of_distinct (a b e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4)
    (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0) :
    integralProfile a b e f g = rationalProfile a b e f g := by
  let z := profileCenters a b e f g
  have hz := profileCenters_bound a b e f g he hf hg
  have hinj := profileCenters_injective a b e f g hab ha hb
  have hs (i : Fin 3 × Bool) : (profilePole z i).im ≠ 0 := by
    rcases i with ⟨i,s⟩
    cases s
    · exact (profilePole_lower z hz i).ne
    · exact (profilePole_upper z hz i).ne'
  have hp := finite_poles_truncation (profilePole z) (profilePole_injective z hz hinj) hs
  rw [profile_pole_sum z hz hinj] at hp
  have hi := intervalIntegral_tendsto_integral (profileIntegrand_integrable a b e f g he hf hg)
    tendsto_neg_atTop_atBot tendsto_id
  dsimp [z] at hp
  simp_rw [← profileIntegrand_eq_poles] at hp
  exact tendsto_nhds_unique hi hp

theorem integralProfile_continuous_gaps (e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    Continuous (fun p : ℝ × ℝ => integralProfile p.1 p.2 e f g) := by
  unfold integralProfile
  apply continuous_of_dominated (F := fun p : ℝ × ℝ => profileIntegrand p.1 p.2 e f g)
    (fun p => (profileIntegrand_integrable p.1 p.2 e f g he hf hg).aestronglyMeasurable)
    (bound := fun t => 64*(1+t^2)⁻¹)
  · intro p
    filter_upwards [] with t
    simpa [div_eq_mul_inv] using profileIntegrand_bound p.1 p.2 e f g t he hf hg
  · exact integrable_inv_one_add_sq.const_mul 64
  · filter_upwards [] with t
    exact (((scalarKernel_continuous e he).comp (continuous_const.sub continuous_fst)).mul
      ((scalarKernel_continuous f hf).comp (continuous_const.sub continuous_snd))).mul continuous_const

theorem rationalProfile_continuous_gaps (e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    Continuous (fun p : ℝ × ℝ => rationalProfile p.1 p.2 e f g) := by
  unfold rationalProfile rationalKernel
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  have hz := profileCenters_bound p.1 p.2 e f g he hf hg
  exact mul_ne_zero (mul_ne_zero (center_quadratic_ne _ _ (hz 0) (hz 1))
    (center_quadratic_ne _ _ (hz 0) (hz 2))) (center_quadratic_ne _ _ (hz 1) (hz 2))

theorem integralProfile_eq (a b e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    integralProfile a b e f g = rationalProfile a b e f g := by
  let S : Finset ℝ := {-a, -b/2, a-b}
  have hd : Dense (Set.univ \ (S : Set ℝ)) := dense_univ.sdiff_finset S
  have hc : Continuous (fun r : ℝ => (a+r,b+2*r)) := by fun_prop
  have h₁ := (integralProfile_continuous_gaps e f g he hf hg).comp hc
  have h₂ := (rationalProfile_continuous_gaps e f g he hf hg).comp hc
  have hh : (fun r : ℝ => integralProfile (a+r) (b+2*r) e f g) =
      (fun r : ℝ => rationalProfile (a+r) (b+2*r) e f g) := by
    apply Continuous.ext_on hd h₁ h₂
    intro r hr
    have hr' : r ≠ -a ∧ r ≠ -b/2 ∧ r ≠ a-b := by simpa [S] using hr.2
    apply integralProfile_eq_of_distinct _ _ _ _ _ he hf hg
    · intro h; exact hr'.2.2 (by linarith)
    · intro h; exact hr'.1 (by linarith)
    · intro h; exact hr'.2.1 (by linarith)
  simpa using congrFun hh 0

end
end HigherCorrelations
