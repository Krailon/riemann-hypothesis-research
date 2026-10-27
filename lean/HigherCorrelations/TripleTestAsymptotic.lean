import HigherCorrelations.TripleTestIdentity

/-! UNCONDITIONAL integrated bound in exact local-spacing units.
R=B^epsilon is substituted into the already checked lower-scale estimates;
no varying-margin limit theorem is invoked. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem tripleTest_observable_lower_scale : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T R X Y : ℝ,
    0 ≤ W → (∀ u, ω u ≤ W) → 3 ≤ T → 1 ≤ R → R ≤ X → R ≤ Y → X*Y ≤ T/R →
    ‖tripleMasterObservable ω T X Y‖ ≤ C*(1+W+fourierDerivativeL1 ω 1)/R*Real.log (2*T+2)^4 := by
  obtain ⟨A,hA,ha⟩ := tripleBudget_uniform_lower_scale
  obtain ⟨B,hB,hb⟩ := tripleInterior_retained_lower_scale
  refine ⟨A+B,by linarith,?_⟩
  intro ω hω W T R X Y hW hw hT hR hX hY hZ
  have he := ha ω hω W T R X Y hW hw hT hR hX hY hZ
  have hm := hb ω hω T R X Y hT hR hX hY hZ
  have hL := tripleBudget_height_log T hT
  have hd := fourierDerivativeL1_nonneg ω 1
  have hp : Real.log (2*T+2)^3 ≤ Real.log (2*T+2)^4 := pow_le_pow_right₀ hL (by omega)
  have hh : B*Real.log (2*T+2)^3/R ≤ B*(1+W+fourierDerivativeL1 ω 1)/R*Real.log (2*T+2)^4 := by
    calc
      _ = (B/R)*Real.log (2*T+2)^3 := by ring
      _ ≤ (B/R)*Real.log (2*T+2)^4 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ := by gcongr; nlinarith
  have ht := norm_le_insert' (tripleMasterObservable ω T X Y) (tripleBudgetRetained ω T X Y)
  exact ht.trans ((add_le_add (hm.trans hh) he).trans_eq (by ring))

theorem tripleTest_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W : ℝ, 0 ≤ W → (∀ u, ω u ≤ W) →
    ∀ (φ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ ε T : ℝ, 0 < ε → ε < 1/3 → 2*Real.pi < T → tsupport φ ⊆ tripleTestMargin ε →
    ‖tripleTestStatistic ω φ T‖ ≤
      C*tripleTestL1 φ*(1+W+fourierDerivativeL1 ω 1)*(tripleTestBase T)^(-ε)*Real.log (2*T+2)^4 := by
  obtain ⟨C,hC,h⟩ := tripleTest_observable_lower_scale
  refine ⟨C,hC,?_⟩
  intro ω hω W hW hw φ hφ hc ε T hε _hεupper hT hs
  let A := C*(1+W+fourierDerivativeL1 ω 1)/(tripleTestBase T)^ε*Real.log (2*T+2)^4
  have hi := tripleTest_frequency_integrable ω hω φ hφ hc ε T hε hT hs
  have hb (p : ℝ × ℝ) : ‖φ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)‖ ≤ ‖φ p‖*A := by
    by_cases hz : φ p=0
    · simp [hz]
    obtain ⟨hr,hx,hy,hxy,hzt⟩ := tripleTest_scale_range ε T p hε hT (hs (subset_tsupport φ hz))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h ω hω W T _ _ _ hW hw (tripleTestBase_bounds T hT).1 hr hx hy hzt) (norm_nonneg _)
  rw [tripleTest_identity ω hω φ hφ hc ε T hε hT hs]
  apply (norm_integral_le_integral_norm _).trans
  have hm := integral_mono hi.norm ((hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hc).norm.mul_const A) hb
  rw [integral_mul_const] at hm
  apply hm.trans_eq
  dsimp [A,tripleTestL1]
  rw [Real.rpow_neg (by linarith [(tripleTestBase_bounds T hT).2.1] : 0 ≤ tripleTestBase T)]
  ring

theorem tripleTest_envelope_tendsto (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun T : ℝ => (tripleTestBase T)^(-ε)*Real.log (2*T+2)^4) atTop (𝓝 0) := by
  have h := (tripleBudgetEnvelope_tendsto ε 0 0 hε le_rfl le_rfl).const_mul ((2*Real.pi)^ε)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (3:ℝ)] with T hT
  unfold tripleBudgetEnvelope tripleTestBase
  rw [Real.div_rpow (by linarith : 0 ≤ T) (by positivity : 0 ≤ 2*Real.pi),
    Real.rpow_neg (by positivity : 0 ≤ 2*Real.pi)]
  simp only [add_zero,one_mul,div_inv_eq_mul]
  ring

theorem tripleTest_fixed_margin_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ε : ℝ) (hε : 0 < ε) (hεupper : ε < 1/3) (hs : tsupport φ ⊆ tripleTestMargin ε) :
    Tendsto (fun T => tripleTestStatistic ω φ T) atTop (𝓝 0) := by
  have hcω : HasCompactSupport ω := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (tripleBudgetWeight_support ω hω)
  obtain ⟨W,hw⟩ := hcω.exists_bound_of_continuous hω.smooth.continuous
  have hW : 0 ≤ W := (norm_nonneg (ω 0)).trans (hw 0)
  have hw' : ∀ u, ω u ≤ W := fun u => (le_abs_self _).trans (by simpa using hw u)
  obtain ⟨C,hC,h⟩ := tripleTest_bound
  have he := (tripleTest_envelope_tendsto ε hε).const_mul (C*tripleTestL1 φ*(1+W+fourierDerivativeL1 ω 1))
  simp only [mul_zero] at he
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) _ he
  filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
  simpa only [mul_assoc] using h ω hω W hW hw' φ hφ hc ε T hε hεupper hT hs

theorem tripleTest_interior_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ tripleTestRegion) :
    Tendsto (fun T => tripleTestStatistic ω φ T) atTop (𝓝 0) := by
  obtain ⟨ε,hε,he,hsε⟩ := tripleTest_compact_margin (tsupport φ) hc hs
  exact tripleTest_fixed_margin_limit ω hω φ hφ hc ε hε he hsε

end
end HigherCorrelations
