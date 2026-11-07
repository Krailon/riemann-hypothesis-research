import HigherCorrelations.SineBenchmarkFunctionalDefinitions
import HigherCorrelations.SignedTestDefinitions
import HigherCorrelations.ProfileTransferDefinitions
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! UNCONDITIONAL compact-test adapter. Positive inverse; complex bilinear tests. -/
namespace HigherCorrelations
noncomputable section
open scoped SchwartzMap FourierTransform

def mainTermFrequencyTest (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) : 𝓢(FourierPlane,ℂ) :=
  (show HasCompactSupport (fun ξ : FourierPlane => φ (planeCoords ξ)) from by
    apply HasCompactSupport.of_support_subset_isCompact
      (planeCoords.toHomeomorph.isClosedEmbedding.isCompact_preimage hc)
    intro ξ hξ
    exact subset_tsupport φ hξ).toSchwartzMap (hφ.comp planeCoords.contDiff)

def mainTermPhysicalTest (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) : 𝓢(FourierPlane,ℂ) := 𝓕⁻ (mainTermFrequencyTest φ hφ hc)

end
end HigherCorrelations
