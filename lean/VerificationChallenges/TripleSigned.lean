import HigherCorrelations.SignedTestDefinitions
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Prod

/-! UNCONDITIONAL independent expected statements. Intentional holes occur only
in verification challenges; project imports are definitions only. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform SchwartzMap

theorem pairZeroTerm_positive_bound (i : ZeroOccurrence) (X t : ℝ) :
    ‖pairZeroTerm i (X,t)‖ ≤ (8/3:ℝ)*Real.exp (|Real.log X|/2)*
      ordinateKernel (t-occurrenceOrdinate i) := by sorry

theorem pairZeroTerm_positive_summable (X t : ℝ) :
    Summable (fun i => ‖pairZeroTerm i (X,t)‖) := by sorry

theorem signedSeries_log_bound (a b x : ℝ) (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.log x| ≤ max |Real.log a| |Real.log b| := by sorry

theorem signedSeries_rectangle_majorant (a b H : ℝ) (ha : 0 < a) :
    ∃ M : ZeroOccurrence → ℝ, Summable M ∧
      ∀ i p, p ∈ signedSeriesRectangle a b H → ‖pairZeroTerm i p‖ ≤ M i := by sorry

theorem signedSeries_uniform_rectangle (a b H : ℝ) (ha : 0 < a) :
    TendstoUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, pairZeroTerm i p)
      pairZeroSeries atTop (signedSeriesRectangle a b H) := by sorry

theorem signedSeries_norm_uniform_rectangle (a b H : ℝ) (ha : 0<a) :
    TendstoUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, ‖pairZeroTerm i p‖)
      (fun p => ∑' i, ‖pairZeroTerm i p‖) atTop (signedSeriesRectangle a b H) := by sorry

theorem signedSeriesRectangle_nhds (p : ℝ × ℝ) (hp : p ∈ signedSeriesDomain) :
    signedSeriesRectangle (p.1/2) (p.1+1) (|p.2|+1) ∈ 𝓝[signedSeriesDomain] p := by sorry

theorem signedSeries_locallyUniform :
    TendstoLocallyUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, pairZeroTerm i p)
      pairZeroSeries atTop signedSeriesDomain := by sorry

theorem signedSeries_norm_locallyUniform :
    TendstoLocallyUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, ‖pairZeroTerm i p‖)
      (fun p => ∑' i, ‖pairZeroTerm i p‖) atTop signedSeriesDomain := by sorry

theorem pairZeroTerm_positive_continuous (i : ZeroOccurrence) :
    ContinuousOn (pairZeroTerm i) signedSeriesDomain := by sorry

theorem signedSeries_continuous : ContinuousOn pairZeroSeries signedSeriesDomain := by sorry

theorem pairZeroTerm_reciprocal (i : ZeroOccurrence) (X t : ℝ) :
    pairZeroTerm (occurrenceReflection i) (X⁻¹,t) = star (pairZeroTerm i (X,t)) := by sorry

theorem pairZeroSeries_reciprocal (X t : ℝ) :
    pairZeroSeries (X⁻¹,t) = star (pairZeroSeries (X,t)) := by sorry

theorem pairZeroSeries_unit_real (t : ℝ) : (pairZeroSeries (1,t)).im=0 := by sorry

theorem tripleMasterCoefficient_positive_bound (X Y : ℝ) (v : MasterTriple) :
    ‖tripleMasterCoefficient X Y v‖ ≤ Real.exp (|Real.log X|+|Real.log Y|) := by sorry

theorem tripleMasterTerm_positive_unit (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (v : MasterTriple) (t : ℝ) :
    tripleMasterTerm ω T X Y v t = tripleMasterCoefficient X Y v*tripleMasterTerm ω T 1 1 v t := by sorry

theorem tripleMasterTerm_positive_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0 < T) (hX : 0 < X) (hY : 0 < Y) (v : MasterTriple) :
    Integrable (tripleMasterTerm ω T X Y v) := by sorry

theorem tripleMaster_positive_integralNorm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3 ≤ T) (hX : 0 < X) (hY : 0 < Y) :
    Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) := by sorry

theorem tripleMaster_positive_pointwise_summable (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3 ≤ T) (hX : 0 < X) (hY : 0 < Y) (t : ℝ) :
    Summable (fun v : MasterTriple => ‖tripleMasterTerm ω T X Y v t‖) := by sorry

theorem tripleMaster_positive_product_eq (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) (t : ℝ) :
    (∑' v : MasterTriple, tripleMasterTerm ω T X Y v t) =
      tripleMasterProduct ω T X Y t := by sorry

theorem tripleMaster_positive_sum_integral (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) :
    (∑' v : MasterTriple, ∫ t : ℝ, tripleMasterTerm ω T X Y v t) =
      ∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω T X Y v t := by sorry

theorem tripleMaster_positive_kernel_identity (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) :
    tripleMasterObservable ω T X Y = 8 * ∑' v : MasterTriple,
      tripleMasterCoefficient X Y v * tripleMasterKernel ω T v := by sorry

theorem tripleMaster_positive_kernel_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) :
    Summable (fun v : MasterTriple => ‖tripleMasterCoefficient X Y v*tripleMasterKernel ω T v‖) := by sorry

theorem tripleMaster_positive_kernel_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      8*∑ v ∈ tripleDomain S, tripleMasterCoefficient X Y v*tripleMasterKernel ω T v)
      atTop (𝓝 (tripleMasterObservable ω T X Y)) := by sorry

theorem signedSectorEquiv_apply (j : Fin 6) (p : ℝ × ℝ) : signedSectorEquiv j p=signedSector j p := by sorry

theorem signedRotation_order_three (p : ℝ × ℝ) :
    signedRotation (signedRotation (signedRotation p))=p := by sorry

theorem signedSector_determinant (j : Fin 6) :
    (signedSector j (1,0)).1*(signedSector j (0,1)).2-
      (signedSector j (0,1)).1*(signedSector j (1,0)).2=1 := by sorry

theorem signedSector_image (j : Fin 6) : signedSector j '' tripleQuadrant=signedSectorCone j := by sorry

theorem signedSector_cover (p : ℝ × ℝ) : ∃ j : Fin 6, p ∈ signedSectorCone j := by sorry

theorem signedSector_overlap (i j : Fin 6) (hij : i ≠ j) (p : ℝ × ℝ)
    (hi : p ∈ signedSectorCone i) (hj : p ∈ signedSectorCone j) : p ∈ signedSectorSeams := by sorry

theorem signedGauge_continuous : Continuous signedGauge := by sorry

theorem signedGauge_nonneg (p : ℝ × ℝ) : 0 ≤ signedGauge p := by sorry

theorem signedGauge_half_sum (p : ℝ × ℝ) :
    signedGauge p=(|p.1|+|p.2|+|p.1+p.2|)/2 := by sorry

theorem signedGauge_sector (j : Fin 6) (p : ℝ × ℝ) (hp : p ∈ tripleQuadrant) :
    signedGauge (signedSector j p)=p.1+p.2 := by sorry

theorem pairZeroSeries_frequency_neg (B x t : ℝ) (hB : 0 < B) :
    pairZeroSeries (B^(-x),t)=star (pairZeroSeries (B^x,t)) := by sorry

theorem tripleMasterProduct_three_frequencies (ω : ℝ → ℝ) (T B x y t : ℝ) (hB : 0 < B) :
    tripleMasterProduct ω T (B^x) (B^y) t =
      (ω (t/T)/T:ℝ)*pairZeroSeries (B^x,t)*pairZeroSeries (B^y,t)*pairZeroSeries (B^(-x-y),t) := by sorry

theorem signedFrequency_rotation (ω : ℝ → ℝ) (T : ℝ) (hT : 2*Real.pi < T) (p : ℝ × ℝ) :
    signedFrequency ω T (signedRotation p)=signedFrequency ω T p := by sorry

theorem signedFrequency_neg (ω : ℝ → ℝ) (T : ℝ) (hT : 2*Real.pi < T) (p : ℝ × ℝ) :
    signedFrequency ω T (-p.1,-p.2)=star (signedFrequency ω T p) := by sorry

theorem signedFrequency_swap (ω : ℝ → ℝ) (T : ℝ) (p : ℝ × ℝ) :
    signedFrequency ω T p.swap=signedFrequency ω T p := by sorry

theorem signedFrequency_sector (ω : ℝ → ℝ) (T : ℝ) (hT : 2*Real.pi < T)
    (j : Fin 6) (p : ℝ × ℝ) :
    signedFrequency ω T (signedSector j p)=
      if j.val < 3 then signedFrequency ω T p else star (signedFrequency ω T p) := by sorry

theorem signedFrequency_seam_real (ω : ℝ → ℝ) (T : ℝ) (hT : 2*Real.pi<T)
    (p : ℝ × ℝ) (hp : p ∈ signedSectorSeams) : star (signedFrequency ω T p)=signedFrequency ω T p := by sorry

theorem tripleMasterProduct_signed_seam_real (ω : ℝ → ℝ) (T B : ℝ) (hB : 0<B)
    (p : ℝ × ℝ) (hp : p ∈ signedSectorSeams) (t : ℝ) :
    star (tripleMasterProduct ω T (B^p.1) (B^p.2) t) =
      tripleMasterProduct ω T (B^p.1) (B^p.2) t := by sorry

theorem signed_horizontal_exponent_bound (p : ℝ × ℝ) (v : MasterTriple) :
    p.1*occurrenceDisplacement (v 0)+p.2*occurrenceDisplacement (v 1)+
      (p.1+p.2)*occurrenceDisplacement (v 2) ≤ signedGauge p := by sorry

theorem signed_coefficient_bound (B : ℝ) (hB : 1 < B) (p : ℝ × ℝ) (v : MasterTriple) :
    ‖tripleMasterCoefficient (B^p.1) (B^p.2) v‖ ≤ B^(signedGauge p) := by sorry

theorem signedFrequencyTerm_bound (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (ε T : ℝ)
    (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε)
    (v : MasterTriple) (p : ℝ × ℝ) :
    ‖tripleTestFrequencyTerm ω φ T v p‖ ≤
      ‖φ p‖*(8*‖tripleMasterKernel ω T (tripleTestToMaster v)‖*(tripleTestBase T)^(1-ε)) := by sorry

theorem signedFrequencyTerm_integrable (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ)
    (hφ : Integrable φ) (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T)
    (hs : tsupport φ ⊆ signedMargin ε) (v : MasterTriple) :
    Integrable (tripleTestFrequencyTerm ω φ T v) := by sorry

theorem signedFrequencyTerm_integralNorm_bound (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ)
    (hφ : Integrable φ) (ε T : ℝ)
    (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) (v : MasterTriple) :
    (∫ p, ‖tripleTestFrequencyTerm ω φ T v p‖) ≤
      tripleTestL1 φ*(8*‖tripleMasterKernel ω T (tripleTestToMaster v)‖*(tripleTestBase T)^(1-ε)) := by sorry

theorem signed_integralNorm_summable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) :
    Summable (fun v : MasterTriple => ∫ p, ‖tripleTestFrequencyTerm ω φ T v p‖) := by sorry

theorem signed_integralNorm_uniform : ∃ A : ℝ, 0 < A ∧ ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ →
    ∀ ε T : ℝ, 0 < ε → 2*Real.pi < T → tsupport φ ⊆ signedMargin ε →
    (∑' v : MasterTriple, ∫ p, ‖tripleTestFrequencyTerm ω φ T v p‖) ≤
      A*tripleTestL1 φ*(tripleTestBase T)^(1-ε)*Real.log (2*T+2)^3 := by sorry

theorem signed_frequency_sum (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (T : ℝ) (hT : 2*Real.pi < T) (p : ℝ × ℝ) :
    (∑' v : MasterTriple, tripleTestFrequencyTerm ω φ T v p) = φ p*signedFrequency ω T p := by sorry

theorem signed_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) :
    tripleTestStatistic ω φ T = ∫ p, φ p*signedFrequency ω T p := by sorry

theorem signed_zero_sum_absolute (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) :
    Summable (fun v : MasterTriple => ‖tripleMasterKernel ω T (tripleTestToMaster v)*
      complexFourier φ (tripleTestArguments T v)‖) := by sorry

theorem signed_frequency_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) :
    Integrable (fun p => φ p*signedFrequency ω T p) := by sorry

theorem signedSector_measurePreserving (j : Fin 6) :
    MeasurePreserving (signedSector j) volume volume := by sorry

theorem signedSector_measurable (j : Fin 6) : MeasurableSet (signedSectorCone j) := by sorry

theorem signedSector_integral (j : Fin 6) (f : ℝ × ℝ → ℂ) :
    (∫ p in signedSectorCone j, f p) = ∫ p in tripleQuadrant, f (signedSector j p) := by sorry

theorem signedSector_seams_null : volume signedSectorSeams = 0 := by sorry

theorem signedSector_partition_integral (f : ℝ × ℝ → ℂ) (hf : Integrable f) :
    (∫ p, f p) = ∑ j : Fin 6, ∫ p in tripleQuadrant, f (signedSector j p) := by sorry

theorem signedSector_disjoint_interiors (i j : Fin 6) (hij : i ≠ j) :
    Disjoint (interior (signedSectorCone i)) (interior (signedSectorCone j)) := by sorry

theorem signedConjugate_involutive (j : Fin 6) (z : ℂ) :
    signedConjugate j (signedConjugate j z)=z := by sorry

theorem signedConjugate_norm (j : Fin 6) (z : ℂ) : ‖signedConjugate j z‖=‖z‖ := by sorry

theorem signedPullback_smooth (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin 6) :
    ContDiff ℝ (⊤ : ℕ∞) (signedPullback φ j) := by sorry

theorem signedPullback_compact (φ : ℝ × ℝ → ℂ) (hc : HasCompactSupport φ) (j : Fin 6) :
    HasCompactSupport (signedPullback φ j) := by sorry

theorem signedPullback_support (φ : ℝ × ℝ → ℂ) (κ : ℝ)
    (hs : tsupport φ ⊆ signedMargin κ) (j : Fin 6) :
    ∀ p ∈ tripleQuadrant, signedPullback φ j p ≠ 0 → p.1+p.2 ≤ 1-κ := by sorry

theorem signed_compact_margin (φ : ℝ × ℝ → ℂ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) : ∃ κ : ℝ, 0<κ ∧ κ<1 ∧ tsupport φ ⊆ signedMargin κ := by sorry

theorem signedSup_bounds (f : ℝ × ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    0 ≤ signedSup f ∧ ∀ p, ‖f p‖ ≤ signedSup f := by sorry

theorem signedPullback_fderiv_norm (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (j : Fin 6) (p v : ℝ × ℝ) :
    ‖fderiv ℝ (signedPullback φ j) p v‖ = ‖fderiv ℝ φ (signedSector j p) (signedSector j v)‖ := by sorry

theorem signedSector_coordinate_norm (j : Fin 6) :
    ‖signedSector j (1,0)‖ ≤ 1 ∧ ‖signedSector j (0,1)‖ ≤ 1 := by sorry

theorem signedPullback_N1_bound (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (j : Fin 6) : tripleQuadrantN1 (signedPullback φ j) ≤ 2*signedC1 φ := by sorry

theorem signedConjugate_integral (j : Fin 6) (f : ℝ × ℝ → ℂ) (μ : Measure (ℝ × ℝ)) :
    signedConjugate j (∫ p, f p ∂μ) = ∫ p, signedConjugate j (f p) ∂μ := by sorry

theorem signedConjugate_div_real (j : Fin 6) (z : ℂ) (r : ℝ) :
    signedConjugate j (z/(r:ℂ)) = signedConjugate j z/(r:ℂ) := by sorry

theorem signed_normalized_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hκ : 0<κ) (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) :
    signedStatistic ω φ T = (∫ p, φ p*signedFrequency ω T p)/(Real.log T:ℂ) := by sorry

theorem signed_zero_identity (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) :
    signedStatistic ω φ T = (8/(Real.log T:ℂ))*
      ∑' v : MasterTriple, tripleMasterKernel ω T (tripleTestToMaster v)*
        complexFourier φ (tripleTestArguments T v) := by sorry

theorem signed_independent_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hκ : 0<κ) (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      (8/(Real.log T:ℂ))*∑ v ∈ tripleDomain S,
        tripleMasterKernel ω T (tripleTestToMaster v)*
          complexFourier φ (tripleTestArguments T v)) atTop
      (𝓝 (signedStatistic ω φ T)) := by sorry

theorem signed_sector_decomposition (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ T : ℝ) (hκ : 0<κ) (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) :
    signedStatistic ω φ T = ∑ j : Fin 6,
      signedConjugate j (tripleQuadrantStatistic ω (signedPullback φ j) T) := by sorry

theorem signed_trace_integrable (φ : ℝ × ℝ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (v : ℝ × ℝ) (hv : v ≠ 0) (w : ℝ → ℂ) (hw : Continuous w) :
    Integrable (fun r : ℝ => w r*φ (r • v)) := by sorry

theorem signed_trace_split (f : ℝ → ℂ) (hf : Integrable (fun r => ((|r|:ℝ):ℂ)*f r)) :
    (∫ r : ℝ, ((|r|:ℝ):ℂ)*f r) = ∫ r : ℝ in Ioi 0, (r:ℂ)*(f r+f (-r)) := by sorry

theorem signed_sector_limit (φ : ℝ × ℝ → ℂ) (j : Fin 6) :
    signedConjugate j (tripleQuadrantLimit (signedPullback φ j)) =
      φ (0,0)/4 + (3/4:ℂ)*∫ r : ℝ in Ioi 0,
        (r:ℂ)*(φ (signedSector j (r,0))+φ (signedSector j (0,r))) := by sorry

theorem signed_limit_sector_sum (φ : ℝ × ℝ → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∑ j : Fin 6, signedConjugate j (tripleQuadrantLimit (signedPullback φ j))) = signedLimit φ := by sorry

theorem signed_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W : ℝ, 0≤W → (∀ u, ω u≤W) →
    ∀ (φ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ T κ : ℝ, 2*Real.pi*Real.exp 1≤T → 0<κ → tsupport φ ⊆ signedMargin κ →
    ‖signedStatistic ω φ T-signedLimit φ‖ ≤
      C*signedC1 φ*(1+W+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) := by sorry

theorem signed_fixed_margin_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => signedStatistic ω φ T) atTop (𝓝 (signedLimit φ)) := by sorry

theorem signed_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => signedStatistic ω φ T) atTop (𝓝 (signedLimit φ)) := by sorry

theorem signed_test_entire (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) : Differentiable ℂ (complexFourier φ) := by sorry

theorem signed_test_schwartz_inversion (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) : ∃ F : 𝓢(FourierPlane,ℂ),
    (∀ x : FourierPlane, F x = complexFourier φ (((planeCoords x).1:ℂ),((planeCoords x).2:ℂ))) ∧
    (∀ ξ : FourierPlane, 𝓕 F ξ = φ (planeCoords ξ)) := by sorry

end
end HigherCorrelations
