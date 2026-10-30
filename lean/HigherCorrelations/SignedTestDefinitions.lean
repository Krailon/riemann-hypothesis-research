import HigherCorrelations.SignedSectorDefinitions
import HigherCorrelations.TripleQuadrantSeminormDefinitions

/-! UNCONDITIONAL full-plane test and normalization conventions. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

def signedConjugate (j : Fin 6) (z : ℂ) : ℂ := if j.val < 3 then z else star z

def signedPullback (φ : ℝ × ℝ → ℂ) (j : Fin 6) (p : ℝ × ℝ) : ℂ :=
  signedConjugate j (φ (signedSector j p))

def signedSup (f : ℝ × ℝ → ℂ) : ℝ := sSup (Set.range (fun p => ‖f p‖))
def signedC1 (φ : ℝ × ℝ → ℂ) : ℝ :=
  signedSup φ + signedSup (fun p => fderiv ℝ φ p (1,0)) +
    signedSup (fun p => fderiv ℝ φ p (0,1))

def signedStatistic (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  tripleTestStatistic ω φ T / (Real.log T : ℂ)

def signedLimit (φ : ℝ × ℝ → ℂ) : ℂ :=
  (3/2:ℂ)*φ (0,0) + (3/2:ℂ)*∫ r : ℝ, ((|r|:ℝ):ℂ)*(φ (r,0)+φ (0,r)+φ (r,-r))

end
end HigherCorrelations
