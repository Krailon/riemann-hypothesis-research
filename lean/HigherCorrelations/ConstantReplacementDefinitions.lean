import HigherCorrelations.ConstantKernelDefinitions
import HigherCorrelations.ActualCorrelationDefinitions
import HigherCorrelations.TripleBudgetDefinitions
import HigherCorrelations.SignedSectorDefinitions

/-! UNCONDITIONAL project-scaled replacement definitions. All sums use ordered
zero occurrences; the Fourier integral is evaluated before the zero sum. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

abbrev ReplacementTriple := Fin 3 → ZeroOccurrence

def replacementDelta (v : ReplacementTriple) : Fin 3 → ℝ :=
  fun j => occurrenceDisplacement (v j)
def replacementRadius (T : ℝ) (v : ReplacementTriple) : ℝ :=
  max |(actualGaps (meanSpacing T) v).1| |(actualGaps (meanSpacing T) v).2|
def replacementHorizontal (T : ℝ) (v : ReplacementTriple) : ℝ :=
  Real.log T * max |replacementDelta v 0| (max |replacementDelta v 1| |replacementDelta v 2|)
def replacementKernel (v : ReplacementTriple) : ℂ :=
  constantKernelEmpty (occurrenceOrdinate (v 1)-occurrenceOrdinate (v 0))
    (occurrenceOrdinate (v 2)-occurrenceOrdinate (v 0)) (replacementDelta v)
def replacementScaleConstant : ℝ := 4096*Real.pi*(32*Real.pi^2+3)

def replacementCosh (b : ℝ) (δ : Fin 3 → ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.cosh (b*δ 0*(p.1+p.2)) * Complex.cosh (b*δ 1*p.1) *
    Complex.cosh (b*δ 2*p.2)-1

def replacementTuple (φ : ℝ × ℝ → ℂ) (T : ℝ) (v : ReplacementTriple) : ℂ :=
  complexFourier (fun p => φ p * replacementCosh (Real.log (T/(2*Real.pi)))
    (replacementDelta v) p)
    (((actualGaps (meanSpacing T) v).1:ℂ), ((actualGaps (meanSpacing T) v).2:ℂ))

def replacementCoordinate (j : Bool) : ℝ × ℝ := if j then (0,1) else (1,0)
def replacementPartial (j : Bool) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun p => fderiv ℝ f p (replacementCoordinate j)
def replacementDeriv (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  (replacementPartial j)^[n] f
/-- Exactly the sum of L1 norms of mixed coordinate partials of total order ≤24. -/
def replacementP24 (φ : ℝ × ℝ → ℂ) : ℝ :=
  ∑ i ∈ Finset.range 25, ∑ j ∈ Finset.range (25-i),
    ∫ p, ‖replacementDeriv false i (replacementDeriv true j φ) p‖

def replacementMomentTerm (ω : ℝ → ℝ) (T s : ℝ) (v : ReplacementTriple) : ℝ :=
  ω (occurrenceOrdinate (v 0)/T) * (replacementHorizontal T v)^2 *
    (1+replacementHorizontal T v)^24 * Real.exp (2*s*replacementHorizontal T v) /
    (1+replacementRadius T v)^20

def replacementMoment (ω : ℝ → ℝ) (T s : ℝ) : ℝ :=
  (∑' v, replacementMomentTerm ω T s v)/(T*Real.log T)
def replacementTerm (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ)
    (v : ReplacementTriple) : ℂ :=
  (ω (occurrenceOrdinate (v 0)/T):ℂ) * (replacementKernel v-kernelBenchmark) *
    replacementTuple φ T v
def replacementError (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  (16/(3*T*Real.log T):ℂ) * ∑' v, replacementTerm ω φ T v
def replacementConstantError (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  (16/(3*T*Real.log T):ℂ) * ∑' v,
    (ω (occurrenceOrdinate (v 0)/T):ℂ)*kernelBenchmark*replacementTuple φ T v
def replacementEvenError (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  (16/(3*T*Real.log T):ℂ) * ∑' v,
    (ω (occurrenceOrdinate (v 0)/T):ℂ)*replacementKernel v*replacementTuple φ T v

def replacementExpRemainder (L : (ℝ × ℝ) →L[ℝ] ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (L p)-1-L p

def replacementSigned (θ : Fin 3 → ℝ) (e : Fin 3 → Bool) (j : Fin 3) : ℝ :=
  if e j then -θ j else θ j

def replacementLinear (θ : Fin 3 → ℝ) (e : Fin 3 → Bool) : (ℝ × ℝ) →L[ℝ] ℂ :=
  ((replacementSigned θ e 0+replacementSigned θ e 1):ℂ) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
  ((replacementSigned θ e 0+replacementSigned θ e 2):ℂ) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))

def replacementDecayConstant : ℝ := (2:ℝ)^22*2^22*23*2^24

end
end HigherCorrelations
