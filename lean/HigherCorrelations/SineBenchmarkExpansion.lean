import HigherCorrelations.SinePrimitivePairings
import HigherCorrelations.SineBenchmarkAlgebra

/-! UNCONDITIONAL finite linearity of absolutely convergent benchmark pairings. -/
namespace HigherCorrelations
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped SchwartzMap FourierTransform

theorem sineDifferenceForm_continuous (j : Fin 3) : Continuous (sineDifferenceForm j) := by
  fin_cases j
  · exact continuous_snd.comp planeCoords.continuous
  · exact continuous_fst.comp planeCoords.continuous
  · exact (continuous_fst.sub continuous_snd).comp planeCoords.continuous

theorem sineLineForm_continuous (j : Fin 3) : Continuous (sineLineForm j) := by
  fin_cases j
  · exact continuous_fst.comp planeCoords.continuous
  · exact continuous_snd.comp planeCoords.continuous
  · exact (continuous_fst.add continuous_snd).comp planeCoords.continuous

theorem sineSquarePlane_integrable (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*(pairMeanSinc (sineDifferenceForm j p):ℂ)^2) :=
  sinePlane_weighted_integrable _ ((Complex.continuous_ofReal.comp
    (pairMeanSinc_continuous.comp (sineDifferenceForm_continuous j))).pow 2)
    1 (fun p => sineSquare_bound _) F

theorem sineTriangle_bound (r : ℝ) : ‖(pairMeanTriangle r:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_max_left 0 _)]
  exact max_le (by norm_num) (by have := abs_nonneg r; linarith)

theorem sineTrianglePlane_integrable (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*(pairMeanTriangle (sineLineForm j p):ℂ)) :=
  sinePlane_weighted_integrable _ (Complex.continuous_ofReal.comp
    (pairMeanTriangle_continuous.comp (sineLineForm_continuous j)))
    1 (fun p => sineTriangle_bound _) F

theorem sineLine_R2_expansion (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineLinePair j sineR2 F = sineLinePair j (fun _ => 1) F-
      sineLinePair j (fun r => (pairMeanSinc r:ℂ)^2) F := by
  simp only [sineLinePair,sineR2,mul_sub,mul_one]
  exact integral_sub (sineLine_integrable j F) (sineSquared_weighted_integrable (sineLineRestriction j F))

theorem sineComplement_m_expansion (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineComplementPair j (fun r => 1-(pairMeanTriangle r:ℂ)) F =
      sineComplementPair j (fun _ => 1) F-sineComplementPair j (fun r => (pairMeanTriangle r:ℂ)) F := by
  simp only [sineComplementPair,mul_sub,mul_one]
  exact integral_sub (sineComplement_integrable j F) (sineTriangle_weighted_integrable (sineComplementRestriction j F))

theorem sineR3_pairing_expansion (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun p => sineR3 (planeCoords p)) F =
      sinePlanePair (fun _ => 1) F-
      (∑ j : Fin 3, sinePlanePair (fun p => (pairMeanSinc (sineDifferenceForm j p):ℂ)^2) F)+
      2*sinePlanePair sineCyclePlane F := by
  have h0 := sineSquarePlane_integrable 0 F
  have h1 := sineSquarePlane_integrable 1 F
  have h2 := sineSquarePlane_integrable 2 F
  have hc := sineCyclePlane_weighted_integrable F
  simp only [sinePlanePair,Fin.sum_univ_three]
  have he : (fun p => F p*sineR3 (planeCoords p)) = fun p =>
      F p-F p*(pairMeanSinc (sineDifferenceForm 0 p):ℂ)^2-
      F p*(pairMeanSinc (sineDifferenceForm 1 p):ℂ)^2-
      F p*(pairMeanSinc (sineDifferenceForm 2 p):ℂ)^2+2*(F p*sineCyclePlane p) := by
    funext p; simp [sineR3,sineDifferenceForm,sineCyclePlane]; ring
  have ha := integral_add (((F.integrable.sub h0).sub h1).sub h2) (hc.const_mul 2)
  have hs2 := integral_sub ((F.integrable.sub h0).sub h1) h2
  have hs1 := integral_sub (F.integrable.sub h0) h1
  have hs0 := integral_sub F.integrable h0
  simp only [Pi.sub_apply,Pi.add_apply] at ha hs2 hs1 hs0
  rw [he,ha,hs2,hs1,hs0,integral_const_mul]
  simp only [mul_one]
  ring

theorem sineCumulantDensity_pairing_expansion (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun p => (sineCumulantDensity (planeCoords p):ℂ)) F =
      sinePlanePair (fun _ => 1) F-
      (∑ j : Fin 3, sinePlanePair (fun p => (pairMeanTriangle (sineLineForm j p):ℂ)) F)+
      2*sinePlanePair sineDensityPlane F := by
  have h0 := sineTrianglePlane_integrable 0 F
  have h1 := sineTrianglePlane_integrable 1 F
  have h2 := sineTrianglePlane_integrable 2 F
  have hc := sineDensityPlane_weighted_integrable F
  simp only [sinePlanePair,Fin.sum_univ_three]
  have he : (fun p => F p*(sineCumulantDensity (planeCoords p):ℂ)) = fun p =>
      F p-F p*(pairMeanTriangle (sineLineForm 0 p):ℂ)-
      F p*(pairMeanTriangle (sineLineForm 1 p):ℂ)-
      F p*(pairMeanTriangle (sineLineForm 2 p):ℂ)+2*(F p*sineDensityPlane p) := by
    funext p; simp [sineCumulantDensity,sineLineForm,sineDensityPlane]; ring
  have ha := integral_add (((F.integrable.sub h0).sub h1).sub h2) (hc.const_mul 2)
  have hs2 := integral_sub ((F.integrable.sub h0).sub h1) h2
  have hs1 := integral_sub (F.integrable.sub h0) h1
  have hs0 := integral_sub F.integrable h0
  simp only [Pi.sub_apply,Pi.add_apply] at ha hs2 hs1 hs0
  rw [he,ha,hs2,hs1,hs0,integral_const_mul]
  simp only [mul_one]
  ring

theorem sineBenchmark_five (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark F = sinePlanePair (fun p => sineR3 (planeCoords p)) F+F 0+
      ∑ j : Fin 3, sineLinePair j sineR2 F := by
  rw [sineBenchmark,show (Finset.univ : Finset TriplePattern) =
    {.allEqual,.only01,.only02,.only12,.allDistinct} from rfl]
  simp [sineBenchmarkRow,Fin.sum_univ_three]
  ring

theorem sineBenchmarkSpectrum_integrable (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*(sineCumulantDensity (planeCoords p):ℂ)) ∧
      ∀ j : Fin 3, Integrable (fun r => F (sineComplement j r)*(1-(pairMeanTriangle r:ℂ))) := by
  constructor
  · have h := (((F.integrable.sub (sineTrianglePlane_integrable 0 F)).sub
      (sineTrianglePlane_integrable 1 F)).sub (sineTrianglePlane_integrable 2 F)).add
      ((sineDensityPlane_weighted_integrable F).const_mul 2)
    convert h using 1
    funext p
    simp [sineCumulantDensity,sineLineForm,sineDensityPlane]
    ring
  · intro j
    have h := (sineComplement_integrable j F).sub
      (sineTriangle_weighted_integrable (sineComplementRestriction j F))
    apply h.congr
    filter_upwards [] with r
    change F (sineComplement j r)-F (sineComplement j r)*(pairMeanTriangle r:ℂ) = _
    ring

end
end HigherCorrelations
