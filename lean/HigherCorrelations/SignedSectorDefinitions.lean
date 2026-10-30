import HigherCorrelations.TripleQuadrantDefinitions
import HigherCorrelations.SignedSeriesDefinitions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! UNCONDITIONAL signed sector conventions, in the archived table's order. -/
namespace HigherCorrelations
noncomputable section
open Set

def signedRotation (p : ℝ × ℝ) : ℝ × ℝ := (p.2,-p.1-p.2)
def signedSector (j : Fin 6) (p : ℝ × ℝ) : ℝ × ℝ :=
  ![p,(p.2,-p.1-p.2),(-p.1-p.2,p.1),(-p.1,-p.2),(-p.2,p.1+p.2),(p.1+p.2,-p.1)] j

def signedSectorInverse (j : Fin 6) : Fin 6 := ![0,2,1,3,5,4] j

def signedSectorEquiv (j : Fin 6) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := signedSector j
    invFun := signedSector (signedSectorInverse j)
    left_inv := by intro p; fin_cases j <;> ext <;> simp [signedSector,signedSectorInverse] <;> ring
    right_inv := by intro p; fin_cases j <;> ext <;> simp [signedSector,signedSectorInverse] <;> ring
    map_add' := by intro p q; fin_cases j <;> ext <;> simp [signedSector] <;> ring
    map_smul' := by intro a p; fin_cases j <;> ext <;> simp [signedSector] <;> ring }

def signedSectorCone (j : Fin 6) : Set (ℝ × ℝ) :=
  ![{p | 0 ≤ p.1 ∧ 0 ≤ p.2}, {p | 0 ≤ p.1 ∧ p.1+p.2 ≤ 0},
    {p | 0 ≤ p.2 ∧ p.1+p.2 ≤ 0}, {p | p.1 ≤ 0 ∧ p.2 ≤ 0},
    {p | p.1 ≤ 0 ∧ 0 ≤ p.1+p.2}, {p | p.2 ≤ 0 ∧ 0 ≤ p.1+p.2}] j

def signedSectorSeams : Set (ℝ × ℝ) := {p | p.1=0 ∨ p.2=0 ∨ p.1+p.2=0}
def signedGauge (p : ℝ × ℝ) : ℝ := max (max |p.1| |p.2|) |p.1+p.2|
def signedRegion : Set (ℝ × ℝ) := {p | signedGauge p < 1}
def signedMargin (κ : ℝ) : Set (ℝ × ℝ) := {p | signedGauge p ≤ 1-κ}
def signedFrequency (ω : ℝ → ℝ) (T : ℝ) (p : ℝ × ℝ) : ℂ :=
  tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)

end
end HigherCorrelations
