import HigherCorrelations.FrozenProfileDefinitions
import HigherCorrelations.SignedTestDefinitions

/-! UNCONDITIONAL definitions of the normalized frozen statistic and its named
localization error. The coefficient already contains 1/T; 8/log T stays outside. -/
namespace HigherCorrelations
noncomputable section

def frozenStatistic (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  (8/(Real.log T:ℂ))*∑' v : MasterTriple,
    tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)

def frozenTransferError (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  (8/(Real.log T:ℂ))*∑' v : MasterTriple,
    tripleKernelLocalizationError ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v)

end
end HigherCorrelations
