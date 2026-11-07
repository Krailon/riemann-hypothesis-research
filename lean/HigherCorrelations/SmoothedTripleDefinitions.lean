import HigherCorrelations.MainTermComparisonDefinitions

/-! UNCONDITIONAL observable and named errors, with full horizontal dependence. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

def smoothedTripleStatistic (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  (2/3:ℂ)*frozenStatistic ω φ T

def smoothedTripleSignedError (φ : ℝ × ℝ → ℂ) (ω : ℝ → ℝ) (M₀ : ℝ) (T κ : ℝ) : ℝ :=
  signedC1 φ*(1+M₀+fourierDerivativeL1 ω 1)*
    (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3)

def smoothedTripleKernelError (φ : ℝ × ℝ → ℂ) (M₀ M₁ T κ : ℝ) : ℝ :=
  tripleTestL1 φ*(M₀+M₁)*(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3

def smoothedWeightSup (ω : ℝ → ℝ) : ℝ := sSup (Set.range (fun x => |ω x|))

def smoothedTripleTerm (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) (v : MasterTriple) : ℂ :=
  (ω (occurrenceOrdinate (v 0)/T):ℂ)*actualRationalKernel v*complexFourier φ (tripleTestArguments T v)

end
end HigherCorrelations
