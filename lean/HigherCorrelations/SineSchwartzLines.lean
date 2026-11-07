import HigherCorrelations.SineSchwartzDefinitions
import HigherCorrelations.SineFourierPairing
import Mathlib.MeasureTheory.Group.Prod

/-! UNCONDITIONAL continuous line restrictions and coordinate-normalized slices. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

theorem sineLineCoords_antilipschitz (j : Fin 3) : AntilipschitzWith 1 (sineLineCoords j) := by
  intro x y
  fin_cases j <;> simp [sineLineCoords,edist_dist,dist_eq_norm,Prod.norm_def]

theorem sineLineRestriction_apply (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) (r : ℝ) :
    sineLineRestriction j F r = F (sineLine j r) := rfl

theorem sineLine_integrable (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun r => F (sineLine j r)) := (sineLineRestriction j F).integrable

theorem sineSlice_measurePreserving (j : Fin 3) : MeasurePreserving (sineSliceMap j) volume volume := by
  have hs : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    simpa [Measure.volume_eq_prod] using Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  have ha : MeasurePreserving (fun p : ℝ × ℝ => (p.1+p.2,-p.1)) volume volume := by
    simpa [Measure.volume_eq_prod,add_comm] using
      (measurePreserving_add_prod_neg (volume : Measure ℝ) (volume : Measure ℝ))
  fin_cases j
  · exact MeasurePreserving.id _
  · exact hs
  · convert ha.comp hs using 1
    ext p <;> simp [sineSliceMap,Function.comp_def,add_comm]

theorem sineSlice_integral (j : Fin 3) (f : ℝ × ℝ → ℂ) :
    (∫ p, f (sineSliceMap j p)) = ∫ p, f p :=
  (sineSlice_measurePreserving j).integral_comp (sineSliceEquiv j).toHomeomorph.measurableEmbedding f

theorem sineSlice_dot (j : Fin 3) (y z r : ℝ) :
    ⟪planeCoords.symm (sineSliceMap j (y,z)), sineLine j r⟫ = y*r := by
  fin_cases j <;> simp [sineLine,sineSliceMap,sineLineCoords,planeCoords,WithLp.prod_inner_apply,Real.inner_apply] <;> ring

theorem sineLine_dot (j : Fin 3) (r : ℝ) (p : FourierPlane) :
    ⟪sineLine j r,p⟫ = r*sineLineForm j p := by
  fin_cases j <;> simp [sineLine,sineLineCoords,sineLineForm,planeCoords,WithLp.prod_inner_apply,Real.inner_apply] <;> ring

theorem sineComplementRestriction_apply (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) (r : ℝ) :
    sineComplementRestriction j F r = F (sineComplement j r) := rfl

theorem sineComplement_integrable (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun r => F (sineComplement j r)) := (sineComplementRestriction j F).integrable

end
end HigherCorrelations
