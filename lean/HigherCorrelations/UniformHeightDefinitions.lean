import HigherCorrelations.LocalZeroCountDefinitions
import HigherCorrelations.ActualCorrelationDefinitions

/-! Definition-only uniform height observables. All tuples are ordered zero occurrences.
The cutoff is closed, so collisions and endpoint multiplicities remain included. -/
namespace HigherCorrelations
noncomputable section
open scoped Classical

def uniformHeightThreshold : ℝ := 2*Real.pi*Real.exp (2*Real.pi)

def anchoredBall (T a R : ℝ) : Finset (AnchoredTriple T) :=
  if h : Set.Finite {t : AnchoredTriple T | anchoredRadius T a t ≤ R}
  then h.toFinset else ∅

def ordinateKernel (x : ℝ) : ℝ := 1/(1+x^2)

def heightIntervalDistance (T t : ℝ) : ℝ := max 0 (max (-t) (t-T))

def zeroKernelSum (t : ℝ) : ℝ := ∑' i : ZeroOccurrence, ordinateKernel (t-occurrenceOrdinate i)

def zeroKernelTail (t a : ℝ) : ℝ :=
  ∑' i : {i : ZeroOccurrence // a ≤ |t-occurrenceOrdinate i|}, ordinateKernel (t-occurrenceOrdinate i)

def normalizedTripleMass (T : ℝ) (f : AnchoredTriple T → ℂ) : ℝ :=
  (∑' t, ‖f t‖)/(T*Real.log T)

def normalizedTripleTail (T a R : ℝ) (f : AnchoredTriple T → ℂ) : ℝ :=
  (∑' t : {t : AnchoredTriple T // R < anchoredRadius T a t}, ‖f t‖)/(T*Real.log T)

abbrev KernelTailOccurrence (t a : ℝ) :=
  {i : ZeroOccurrence // a ≤ |t-occurrenceOrdinate i|}

def kernelTailRadius (t a : ℝ) (i : KernelTailOccurrence t a) : ℝ :=
  (|t-occurrenceOrdinate i.val|-a)/(1+a)


abbrev AnchoredTail (T a R : ℝ) := {t : AnchoredTriple T // R ≤ anchoredRadius T a t}

def anchoredTailRadius (T a R : ℝ) (t : AnchoredTail T a R) : ℝ :=
  (anchoredRadius T a t.val-R)/(1+R)


end
end HigherCorrelations
