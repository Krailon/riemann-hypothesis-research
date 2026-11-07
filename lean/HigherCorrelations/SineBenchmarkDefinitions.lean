import HigherCorrelations.SineFourierDefinitions
import HigherCorrelations.FiniteDefinitions
import Mathlib.Analysis.Distribution.TemperedDistribution

/-! UNCONDITIONAL definitions for the five occurrence-index benchmark partitions.
All line measures use the displayed coordinate, not arclength. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform

def sineR2 (r : ℝ) : ℂ := 1-(pairMeanSinc r:ℂ)^2
def sineR3 (p : ℝ × ℝ) : ℂ := 1-(pairMeanSinc p.1:ℂ)^2-
  (pairMeanSinc p.2:ℂ)^2-(pairMeanSinc (p.1-p.2):ℂ)^2+2*sineCycle p
def sineCumulantDensity (p : ℝ × ℝ) : ℝ :=
  1-pairMeanTriangle p.1-pairMeanTriangle p.2-pairMeanTriangle (p.1+p.2)+
    2*sineCycleDensity p.1 p.2

def sineLineCoords (j : Fin 3) : ℝ →L[ℝ] ℝ × ℝ :=
  ![(ContinuousLinearMap.id ℝ ℝ).prod 0, (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ),
    (ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)] j

def sineSliceMap (j : Fin 3) (p : ℝ × ℝ) : ℝ × ℝ :=
  ![p,(p.2,p.1),(p.1+p.2,-p.2)] j

def sineSliceEquiv (j : Fin 3) : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := sineSliceMap j
    invFun := sineSliceMap j
    left_inv := by intro p; fin_cases j <;> ext <;> simp [sineSliceMap] <;> ring
    right_inv := by intro p; fin_cases j <;> ext <;> simp [sineSliceMap] <;> ring
    map_add' := by intro p q; fin_cases j <;> ext <;> simp [sineSliceMap] <;> ring
    map_smul' := by intro a p; fin_cases j <;> ext <;> simp [sineSliceMap] <;> ring }

def sineLine (j : Fin 3) (r : ℝ) : FourierPlane := planeCoords.symm (sineLineCoords j r)
def sineComplement (j : Fin 3) (r : ℝ) : FourierPlane := planeCoords.symm (sineSliceMap j (0,r))
def sineLineForm (j : Fin 3) (p : FourierPlane) : ℝ :=
  ![(planeCoords p).1,(planeCoords p).2,(planeCoords p).1+(planeCoords p).2] j

def sineMarginal (F : 𝓢(ℝ × ℝ,ℂ)) (y : ℝ) : ℂ := ∫ z : ℝ, F (y,z)

def sineDirectionCLM (a b : ℝ) : ℝ →L[ℝ] FourierPlane :=
  planeCoords.symm.toContinuousLinearMap.comp
    ((a • ContinuousLinearMap.id ℝ ℝ).prod (b • ContinuousLinearMap.id ℝ ℝ))
def sineDirection (a b r : ℝ) : FourierPlane := sineDirectionCLM a b r
def sineDirectionForm (a b : ℝ) (p : FourierPlane) : ℝ := a*(planeCoords p).1+b*(planeCoords p).2

end
end HigherCorrelations
