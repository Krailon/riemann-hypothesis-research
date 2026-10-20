import HigherCorrelations.PairRHSDefinitions
import HigherCorrelations.Zeta23Definitions
import HigherCorrelations.IntegralProfileDefinitions

/-! UNCONDITIONAL definition-only zero-side interface. All ordered pairs and
multiplicity indices are retained. Windows are (0,T], cutoffs are |gamma| <= Z. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

def pairKernelProduct (a e f t : ℝ) : ℂ := scalarKernel (t-a) e * scalarKernel t f
def pairKernelIntegral (a e f : ℝ) : ℂ := ∫ t : ℝ, pairKernelProduct a e f t
def pairKernelValue (a e f : ℝ) : ℂ :=
  2 * Real.pi / (4 + ((a : ℂ) + Complex.I*(f-e))^2)
def pairKernelCenters (a e f : ℝ) : Fin 2 → ℂ :=
  ![(a : ℂ)-Complex.I*e, -Complex.I*f]
def pairKernelPole (z : Fin 2 → ℂ) (i : Fin 2 × Bool) : ℂ :=
  z i.1 + if i.2 then Complex.I else -Complex.I

def pairZeroVector (i : ZeroOccurrence) (X t : ℝ) : ℂ :=
  Complex.exp ((Real.log X : ℂ) *
    ((occurrenceDisplacement i : ℂ) + Complex.I * occurrenceOrdinate i)) *
    scalarKernel (t-occurrenceOrdinate i) (occurrenceDisplacement i)
def pairZeroFullVector (X t : ℝ) : ℂ := ∑' i, pairZeroVector i X t
def pairZeroCutoffVector (X Z t : ℝ) : ℂ := ∑ i ∈ occurrenceCutoff Z, pairZeroVector i X t
def pairZeroWindowVector (X T t : ℝ) : ℂ := ∑ i ∈ occurrenceWindow 0 T, pairZeroVector i X t
def pairCorrelationSum (X T : ℝ) : ℂ :=
  ∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
    Complex.exp ((Real.log X : ℂ) * (occurrenceValue i-occurrenceValue j)) *
      (4 / (4-(occurrenceValue i-occurrenceValue j)^2))
def pairZeroTruncError (X T Z : ℝ) : ℝ :=
  4 * ∫ t in (0:ℝ)..T, ‖pairZeroFullVector X t‖^2 - ‖pairZeroCutoffVector X Z t‖^2
def pairZeroHeightError (X T Z : ℝ) : ℝ :=
  4 * ∫ t in (0:ℝ)..T, ‖pairZeroCutoffVector X Z t‖^2 - ‖pairZeroWindowVector X T t‖^2
def pairZeroExtensionError (X T : ℝ) : ℝ :=
  -4 * ∫ t in (Set.Icc (0:ℝ) T)ᶜ, ‖pairZeroWindowVector X T t‖^2

end
end HigherCorrelations
