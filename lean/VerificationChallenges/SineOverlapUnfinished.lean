import HigherCorrelations.SineBenchmarkFunctionalDefinitions
import HigherCorrelations.SineSchwartzDefinitions

/-! UNCONDITIONAL independent statements. Intentional holes occur only in
verification challenges. No solution proof module is imported. -/
namespace HigherCorrelations
noncomputable section
open Set MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem sineOverlap_translated (ξ η : ℝ) :
    sineOverlap ξ η = sineInterval ∩ ((fun d : ℝ => ξ+d) '' sineInterval) ∩
      ((fun d : ℝ => -η+d) '' sineInterval) := by sorry

theorem sineOverlap_interval (ξ η : ℝ) :
    sineOverlap ξ η = Icc (max (max 0 ξ) (-η)-1/2)
      (min (min 0 ξ) (-η)+1/2) := by sorry

theorem sineOverlap_span (ξ η : ℝ) :
    max (max 0 ξ) (-η)-min (min 0 ξ) (-η) = signedGauge (ξ,η) := by sorry

theorem sineOverlap_volume (ξ η : ℝ) :
    volume (sineOverlap ξ η) = ENNReal.ofReal (1-signedGauge (ξ,η)) := by sorry

theorem sineOverlap_length (ξ η : ℝ) :
    sineOverlapLength ξ η = sineCycleDensity ξ η := by sorry

theorem sineOverlap_measurable (ξ η : ℝ) : MeasurableSet (sineOverlap ξ η) := by sorry

theorem sineOverlap_finite (ξ η : ℝ) : volume (sineOverlap ξ η) < ⊤ := by sorry

theorem sineOverlapIntegrand_indicator (ξ η : ℝ) :
    sineOverlapIntegrand ξ η = (sineOverlap ξ η).indicator (fun _ => (1:ℝ)) := by sorry

theorem sineOverlapIntegrand_integrable (ξ η : ℝ) : Integrable (sineOverlapIntegrand ξ η) := by sorry

theorem sineOverlap_integral (ξ η : ℝ) :
    (∫ d : ℝ, sineOverlapIntegrand ξ η d) = sineCycleDensity ξ η := by sorry

theorem sineOverlap_nonempty (ξ η : ℝ) :
    (sineOverlap ξ η).Nonempty ↔ signedGauge (ξ,η) ≤ 1 := by sorry

theorem sineOverlap_touching (ξ η : ℝ) (h : signedGauge (ξ,η) = 1) :
    sineOverlap ξ η = {max (max 0 ξ) (-η)-1/2} := by sorry

theorem sineOverlap_empty (ξ η : ℝ) (h : 1 < signedGauge (ξ,η)) :
    sineOverlap ξ η = ∅ := by sorry

theorem sineOverlap_length_pos (ξ η : ℝ) :
    0 < sineOverlapLength ξ η ↔ signedGauge (ξ,η) < 1 := by sorry

theorem sineOverlap_length_zero (ξ η : ℝ) (h : 1 ≤ signedGauge (ξ,η)) :
    sineOverlapLength ξ η = 0 := by sorry

theorem sineOverlap_length_sector (j : Fin 6) (p : ℝ × ℝ) (hp : p ∈ tripleQuadrant) :
    sineOverlapLength (signedSector j p).1 (signedSector j p).2 = max 0 (1-p.1-p.2) := by sorry

theorem sineOverlap_length_axes (r : ℝ) :
    sineOverlapLength r 0 = max 0 (1-|r|) ∧
    sineOverlapLength 0 r = max 0 (1-|r|) ∧
    sineOverlapLength r (-r) = max 0 (1-|r|) := by sorry

theorem sineOverlap_length_origin : sineOverlapLength 0 0 = 1 := by sorry

theorem sineOverlap_length_repeated (r : ℝ) :
    sineOverlapLength r (-r) = max 0 (1-|r|) := by sorry

theorem sineOverlap_length_examples :
    sineOverlapLength (1/4) (1/4) = 1/2 ∧
    sineOverlapLength (3/4) (3/4) = 0 ∧
    sineOverlapLength 1 0 = 0 := by sorry

theorem sineCycle_continuous : Continuous sineCycle := by sorry

theorem sineCycle_bound (p : ℝ × ℝ) : ‖sineCycle p‖ ≤ 1 := by sorry

theorem sineCycle_reflection (p : ℝ × ℝ) : sineCycle (-p) = sineCycle p := by sorry

theorem sineCycle_origin : sineCycle (0,0) = 1 := by sorry

theorem sineCycle_axes (r : ℝ) :
    sineCycle (r,0) = (pairMeanSinc r:ℂ)^2 ∧
    sineCycle (0,r) = (pairMeanSinc r:ℂ)^2 ∧
    sineCycle (r,r) = (pairMeanSinc r:ℂ)^2 := by sorry

theorem sineCycleDensity_bounds (ξ η : ℝ) : 0 ≤ sineCycleDensity ξ η ∧ sineCycleDensity ξ η ≤ 1 := by sorry

theorem sineCycleDensity_reflection (ξ η : ℝ) : sineCycleDensity (-ξ) (-η) = sineCycleDensity ξ η := by sorry

theorem sineCycleDensity_continuous : Continuous (fun p : ℝ × ℝ => sineCycleDensity p.1 p.2) := by sorry

theorem sineCycleDensity_compactSupport : HasCompactSupport (fun p : ℝ × ℝ => sineCycleDensity p.1 p.2) := by sorry

theorem sineCycleDensity_integrable : Integrable (fun p : ℝ × ℝ => sineCycleDensity p.1 p.2) := by sorry

theorem sineDensityPlane_integrable : Integrable sineDensityPlane := by sorry

theorem sineCyclePlane_weighted_integrable (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun x => F x*sineCyclePlane x) := by sorry

theorem sineDensityPlane_weighted_integrable (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun x => F x*sineDensityPlane x) := by sorry

theorem sineParameterIntegrand_majorant (u v : ℝ) (q : ℝ × (ℝ × ℝ)) :
    ‖sineParameterIntegrand u v q‖ ≤
      (sineInterval ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)).indicator (fun _ => (1:ℝ)) q := by sorry

theorem sineParameterIntegrand_integrable (u v : ℝ) : Integrable (sineParameterIntegrand u v) := by sorry

theorem sineParameterIntegrand_fubini (u v : ℝ) :
    (∫ p : ℝ × ℝ, ∫ d : ℝ, sineParameterIntegrand u v (d,p)) =
      ∫ d : ℝ, ∫ p : ℝ × ℝ, sineParameterIntegrand u v (d,p) := by sorry

theorem sineParameterIntegrand_inner (u v : ℝ) (p : ℝ × ℝ) :
    (∫ d : ℝ, sineParameterIntegrand u v (d,p)) =
      (sineCycleDensity p.1 p.2 : ℂ) * pairMeanCharacter (u*p.1+v*p.2) := by sorry

theorem sineInterval_character (u : ℝ) :
    (∫ a : ℝ, pairMeanBox a * pairMeanCharacter (u*a)) = (pairMeanSinc u : ℂ) := by sorry

theorem sineParameterIntegrand_plane_integral (u v d : ℝ) :
    (∫ p : ℝ × ℝ, sineParameterIntegrand u v (d,p)) =
      pairMeanBox d*pairMeanCharacter ((u-v)*d)*(pairMeanSinc u:ℂ)*(pairMeanSinc v:ℂ) := by sorry

theorem sineCycleDensity_inverse_integral (u v : ℝ) :
    (∫ p : ℝ × ℝ, (sineCycleDensity p.1 p.2:ℂ)*pairMeanCharacter (u*p.1+v*p.2)) =
      sineCycle (u,v) := by sorry

theorem sineDensityPlane_inverse (x : FourierPlane) :
    (𝓕⁻ sineDensityPlane) x = sineCyclePlane x := by sorry

theorem sineDensityPlane_fourier (x : FourierPlane) :
    (𝓕 sineDensityPlane) x = sineCyclePlane x := by sorry

theorem sineDensityPlane_mass : (∫ x : FourierPlane, sineDensityPlane x) = 1 := by sorry

theorem sineCycle_pairing (F : 𝓢(FourierPlane,ℂ)) :
    (∫ x, F x*sineCyclePlane x) = ∫ ξ, (𝓕 F) ξ*sineDensityPlane ξ := by sorry

theorem sineCycle_inverse_pairing (φ : 𝓢(FourierPlane,ℂ)) :
    (∫ x, (𝓕⁻ φ) x*sineCyclePlane x) = ∫ ξ, φ ξ*sineDensityPlane ξ := by sorry

theorem sineSquared_weighted_integrable (F : 𝓢(ℝ,ℂ)) :
    Integrable (fun x => F x*(pairMeanSinc x:ℂ)^2) := by sorry

theorem sineTriangle_weighted_integrable (F : 𝓢(ℝ,ℂ)) :
    Integrable (fun ξ => F ξ*(pairMeanTriangle ξ:ℂ)) := by sorry

theorem sineSquared_pairing (F : 𝓢(ℝ,ℂ)) :
    (∫ x, F x*(pairMeanSinc x:ℂ)^2) = ∫ ξ, (𝓕 F) ξ*(pairMeanTriangle ξ:ℂ) := by sorry

theorem sineSquared_inverse_pairing (φ : 𝓢(ℝ,ℂ)) :
    (∫ x, (𝓕⁻ φ) x*(pairMeanSinc x:ℂ)^2) = ∫ ξ, φ ξ*(pairMeanTriangle ξ:ℂ) := by sorry

theorem sineLineCoords_antilipschitz (j : Fin 3) : AntilipschitzWith 1 (sineLineCoords j) := by sorry

theorem sineLineRestriction_apply (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) (r : ℝ) :
    sineLineRestriction j F r = F (sineLine j r) := by sorry

theorem sineLine_integrable (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun r => F (sineLine j r)) := by sorry

theorem sineSlice_measurePreserving (j : Fin 3) : MeasurePreserving (sineSliceMap j) volume volume := by sorry

theorem sineSlice_integral (j : Fin 3) (f : ℝ × ℝ → ℂ) :
    (∫ p, f (sineSliceMap j p)) = ∫ p, f p := by sorry

theorem sineSlice_dot (j : Fin 3) (y z r : ℝ) :
    ⟪planeCoords.symm (sineSliceMap j (y,z)), sineLine j r⟫ = y*r := by sorry

theorem sineLine_dot (j : Fin 3) (r : ℝ) (p : FourierPlane) :
    ⟪sineLine j r,p⟫ = r*sineLineForm j p := by sorry

theorem sineComplementRestriction_apply (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) (r : ℝ) :
    sineComplementRestriction j F r = F (sineComplement j r) := by sorry

theorem sineComplement_integrable (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun r => F (sineComplement j r)) := by sorry

theorem sineMarginal_majorant (F : 𝓢(ℝ × ℝ,ℂ)) :
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ y z, ‖F (y,z)‖ ≤ B z := by sorry

theorem sineMarginal_continuous (F : 𝓢(ℝ × ℝ,ℂ)) : Continuous (sineMarginal F) := by sorry

theorem sineMarginal_integrable (F : 𝓢(ℝ × ℝ,ℂ)) : Integrable (sineMarginal F) := by sorry

theorem sineMarginal_fourier (F : 𝓢(ℝ × ℝ,ℂ)) (r : ℝ) :
    pairMeanFourier (sineMarginal F) r =
      ∫ p : ℝ × ℝ, pairMeanCharacter (-p.1*r)*F p := by sorry

theorem sineSlice_fourier_marginal (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) (r : ℝ) :
    let G := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (sineSliceEquiv j)
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeCoords.symm F)
    (𝓕 (sineMarginal G)) r = (𝓕 F) (sineLine j r) := by sorry

theorem sineLine_fourier_integral (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r : ℝ, (𝓕 F) (sineLine j r)) = ∫ r : ℝ, F (sineComplement j r) := by sorry

theorem sineDirection_dot (a b r : ℝ) (p : FourierPlane) :
    ⟪sineDirection a b r,p⟫ = r*sineDirectionForm a b p := by sorry

theorem sineDirection_fourier_duality (a b : ℝ) (f : ℝ → ℂ) (hf : Integrable f)
    (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r, (𝓕 F) (sineDirection a b r)*f r) =
      ∫ p, F p*pairMeanFourier f (sineDirectionForm a b p) := by sorry

theorem sineDirection_square_pairing (a b : ℝ) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r, (𝓕 F) (sineDirection a b r)*(pairMeanSinc r:ℂ)^2) =
      ∫ p, F p*(pairMeanTriangle (sineDirectionForm a b p):ℂ) := by sorry

theorem sineDirection_triangle_pairing (a b : ℝ) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r, (𝓕 F) (sineDirection a b r)*(pairMeanTriangle r:ℂ)) =
      ∫ p, F p*(pairMeanSinc (sineDirectionForm a b p):ℂ)^2 := by sorry

theorem sinePlane_weighted_integrable (f : FourierPlane → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ p, ‖f p‖ ≤ C) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*f p) := by sorry

theorem sineLine_weighted_integrable (j : Fin 3) (w : ℝ → ℂ) (hw : Continuous w)
    (C : ℝ) (hC : ∀ r, ‖w r‖ ≤ C) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun r => F (sineLine j r)*w r) := by sorry

theorem sinePlane_tempered (f : FourierPlane → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ p, ‖f p‖ ≤ C) :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sinePlanePair f F := by sorry

theorem sineLine_tempered (j : Fin 3) (w : ℝ → ℂ) (hw : Continuous w)
    (C : ℝ) (hC : ∀ r, ‖w r‖ ≤ C) :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineLinePair j w F := by sorry

theorem sineSquare_bound (r : ℝ) : ‖(pairMeanSinc r:ℂ)^2‖ ≤ 1 := by sorry

theorem sineR2_continuous : Continuous sineR2 := by sorry

theorem sineR2_bound (r : ℝ) : ‖sineR2 r‖ ≤ 2 := by sorry

theorem sineR3_continuous : Continuous (fun p : FourierPlane => sineR3 (planeCoords p)) := by sorry

theorem sineR3_bound (p : ℝ × ℝ) : ‖sineR3 p‖ ≤ 6 := by sorry

theorem sineFourier_twice (F : 𝓢(FourierPlane,ℂ)) (x : FourierPlane) :
    (𝓕 (𝓕 F)) x = F (-x) := by sorry

theorem sineDirection_triangle_reflection (a b : ℝ) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r, F (-sineDirection a b r)*(pairMeanTriangle r:ℂ)) =
      ∫ r, F (sineDirection a b r)*(pairMeanTriangle r:ℂ) := by sorry

theorem sineDirection_plane_square_pairing (a b : ℝ) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ p, (𝓕 F) p*(pairMeanSinc (sineDirectionForm a b p):ℂ)^2) =
      ∫ r, F (sineDirection a b r)*(pairMeanTriangle r:ℂ) := by sorry

theorem sineLine_square_fourier (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineLinePair j (fun r => (pairMeanSinc r:ℂ)^2) (𝓕 F) =
      sinePlanePair (fun p => (pairMeanTriangle (sineLineForm j p):ℂ)) F := by sorry

theorem sinePlane_square_fourier (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun p => (pairMeanSinc (sineDifferenceForm j p):ℂ)^2) (𝓕 F) =
      sineComplementPair j (fun r => (pairMeanTriangle r:ℂ)) F := by sorry

theorem sineLine_constant_fourier (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineLinePair j (fun _ => 1) (𝓕 F) = sineComplementPair j (fun _ => 1) F := by sorry

theorem sinePlane_constant_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun _ => 1) (𝓕 F) = F 0 := by sorry

theorem sineAtom_fourier (F : 𝓢(FourierPlane,ℂ)) :
    (𝓕 F) 0 = sinePlanePair (fun _ => 1) F := by sorry

theorem sineCycle_distribution_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair sineCyclePlane (𝓕 F) = sinePlanePair sineDensityPlane F := by sorry

theorem sineR3_determinant (u v : ℝ) :
    Matrix.det !![(1:ℂ), (pairMeanSinc u:ℂ), (pairMeanSinc v:ℂ);
      (pairMeanSinc u:ℂ), 1, (pairMeanSinc (u-v):ℂ);
      (pairMeanSinc v:ℂ), (pairMeanSinc (u-v):ℂ), 1] = sineR3 (u,v) := by sorry

theorem sineCumulantDensity_closed (p : ℝ × ℝ) (hp : signedGauge p ≤ 1) :
    sineCumulantDensity p = 0 := by sorry

theorem sineCumulantDensity_exterior : sineCumulantDensity (3/4,3/4) = 1/2 := by sorry

theorem sineFactorialDensity_origin : 2*sineCycleDensity 0 0 = 2 := by sorry

theorem sineCumulants_distinct : sineCumulantDensity (0,0) ≠ 2*sineCycleDensity 0 0 := by sorry

theorem sineR3_factorial_identity (u v : ℝ) :
    sineR3 (u,v)-sineR2 u-sineR2 v-sineR2 (u-v)+2 = 2*sineCycle (u,v) := by sorry

theorem sineFactorialDensity_positive (p : ℝ × ℝ) (hp : signedGauge p < 1) :
    0 < 2*sineCycleDensity p.1 p.2 := by sorry

theorem sineDifferenceForm_continuous (j : Fin 3) : Continuous (sineDifferenceForm j) := by sorry

theorem sineLineForm_continuous (j : Fin 3) : Continuous (sineLineForm j) := by sorry

theorem sineSquarePlane_integrable (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*(pairMeanSinc (sineDifferenceForm j p):ℂ)^2) := by sorry

theorem sineTriangle_bound (r : ℝ) : ‖(pairMeanTriangle r:ℂ)‖ ≤ 1 := by sorry

theorem sineTrianglePlane_integrable (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*(pairMeanTriangle (sineLineForm j p):ℂ)) := by sorry

theorem sineLine_R2_expansion (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineLinePair j sineR2 F = sineLinePair j (fun _ => 1) F-
      sineLinePair j (fun r => (pairMeanSinc r:ℂ)^2) F := by sorry

theorem sineComplement_m_expansion (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineComplementPair j (fun r => 1-(pairMeanTriangle r:ℂ)) F =
      sineComplementPair j (fun _ => 1) F-sineComplementPair j (fun r => (pairMeanTriangle r:ℂ)) F := by sorry

theorem sineR3_pairing_expansion (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun p => sineR3 (planeCoords p)) F =
      sinePlanePair (fun _ => 1) F-
      (∑ j : Fin 3, sinePlanePair (fun p => (pairMeanSinc (sineDifferenceForm j p):ℂ)^2) F)+
      2*sinePlanePair sineCyclePlane F := by sorry

theorem sineCumulantDensity_pairing_expansion (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun p => (sineCumulantDensity (planeCoords p):ℂ)) F =
      sinePlanePair (fun _ => 1) F-
      (∑ j : Fin 3, sinePlanePair (fun p => (pairMeanTriangle (sineLineForm j p):ℂ)) F)+
      2*sinePlanePair sineDensityPlane F := by sorry

theorem sineBenchmark_five (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark F = sinePlanePair (fun p => sineR3 (planeCoords p)) F+F 0+
      ∑ j : Fin 3, sineLinePair j sineR2 F := by sorry

theorem sineBenchmarkSpectrum_integrable (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*(sineCumulantDensity (planeCoords p):ℂ)) ∧
      ∀ j : Fin 3, Integrable (fun r => F (sineComplement j r)*(1-(pairMeanTriangle r:ℂ))) := by sorry

theorem sineBenchmark_partial_fourier (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineLinePair j sineR2 (𝓕 F) = sineComplementPair j (fun _ => 1) F-
      sinePlanePair (fun p => (pairMeanTriangle (sineLineForm j p):ℂ)) F := by sorry

theorem sineBenchmark_distinct_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun p => sineR3 (planeCoords p)) (𝓕 F) = F 0-
      (∑ j : Fin 3, sineComplementPair j (fun r => (pairMeanTriangle r:ℂ)) F)+
      2*sinePlanePair sineDensityPlane F := by sorry

theorem sineBenchmarkRow_fourier (k : TriplePattern) (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmarkRow k (𝓕 F) = sineBenchmarkFourierRow k F := by sorry

theorem sineBenchmark_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark (𝓕 F) = sineBenchmarkSpectrum F := by sorry

theorem sineOrdinaryCumulant_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sineOrdinaryCumulant (𝓕 F) = sinePlanePair (fun p => (sineCumulantDensity (planeCoords p):ℂ)) F := by sorry

theorem sineFactorialCumulant_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sineFactorialCumulant (𝓕 F) = 2*sinePlanePair sineDensityPlane F := by sorry

theorem sineBenchmark_moment_cumulant (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark F = sinePlanePair (fun _ => 1) F+
      (∑ j : Fin 3, sineCovarianceLift j F)+sineOrdinaryCumulant F := by sorry

theorem sineBenchmark_tempered :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineBenchmark F := by sorry

theorem sineOrdinaryCumulant_tempered :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineOrdinaryCumulant F := by sorry

theorem sineFactorialCumulant_tempered :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineFactorialCumulant F := by sorry

theorem sineBenchmark_distribution_fourier (D : 𝓢'(FourierPlane,ℂ))
    (hD : ∀ F, D F = sineBenchmark F) (F : 𝓢(FourierPlane,ℂ)) :
    (𝓕 D) F = sineBenchmarkSpectrum F := by sorry

theorem sineOrdinaryCumulant_distribution_fourier (D : 𝓢'(FourierPlane,ℂ))
    (hD : ∀ F, D F = sineOrdinaryCumulant F) (F : 𝓢(FourierPlane,ℂ)) :
    (𝓕 D) F = sinePlanePair (fun p => (sineCumulantDensity (planeCoords p):ℂ)) F := by sorry

theorem sineFactorialCumulant_distribution_fourier (D : 𝓢'(FourierPlane,ℂ))
    (hD : ∀ F, D F = sineFactorialCumulant F) (F : 𝓢(FourierPlane,ℂ)) :
    (𝓕 D) F = 2*sinePlanePair sineDensityPlane F := by sorry

theorem sineBenchmark_integrable (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*sineR3 (planeCoords p)) ∧
      ∀ j : Fin 3, Integrable (fun r => F (sineLine j r)*sineR2 r) := by sorry

theorem sineBenchmark_continuous : Continuous sineBenchmark := by sorry

theorem sineOrdinaryCumulant_continuous : Continuous sineOrdinaryCumulant := by sorry

theorem sineFactorialCumulant_continuous : Continuous sineFactorialCumulant := by sorry

theorem sineBenchmarkRow_tempered (k : TriplePattern) :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineBenchmarkRow k F := by sorry

theorem sineCovarianceLift_tempered (j : Fin 3) :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineCovarianceLift j F := by sorry

theorem sineBenchmark_distribution_moment_cumulant
    (M O : 𝓢'(FourierPlane,ℂ)) (C : Fin 3 → 𝓢'(FourierPlane,ℂ))
    (hM : ∀ F, M F = sineBenchmark F) (hO : ∀ F, O F = sineOrdinaryCumulant F)
    (hC : ∀ j F, C j F = sineCovarianceLift j F) :
    M = (volume : Measure FourierPlane).toTemperedDistribution + (∑ j, C j) + O := by sorry

theorem sineBenchmark_manuscript (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark F = (∫ p, F p*sineR3 (planeCoords p))+F 0+
      ∫ r, sineR2 r*(F (sineLine 1 r)+F (sineLine 0 r)+F (sineLine 2 r)) := by sorry

end
end HigherCorrelations
