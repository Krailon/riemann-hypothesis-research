import HigherCorrelations.PairSeriesDefinitions
import HigherCorrelations.FiniteDefinitions
import HigherCorrelations.UniformHeightDefinitions

/-! UNCONDITIONAL definition-only interface for the triple master interchange.
All ordered actual occurrences, both ordinate signs, and multiplicities are retained.
Slots 0,1,2 correspond to manuscript indices j,k,l; slot 2 is conjugated. -/
namespace HigherCorrelations
noncomputable section

abbrev MasterTriple := Fin 3 → ZeroOccurrence

def tripleMasterTerm (ω : ℝ → ℝ) (T X Y : ℝ) (v : MasterTriple) (t : ℝ) : ℂ :=
  (ω (t/T)/T : ℝ)*pairZeroTerm (v 0) (X,t)*pairZeroTerm (v 1) (Y,t)*
    star (pairZeroTerm (v 2) (X*Y,t))

def tripleMasterMajorant (C₀ : ℝ) (ω : ℝ → ℝ) (T X Y t : ℝ) : ℝ :=
  (8/3 : ℝ)^3*C₀^3*X*Y*Real.log (2*T+2)^3*(|ω (t/T)|/T)

def tripleMasterL1Bound (C₀ : ℝ) (ω : ℝ → ℝ) (T X Y : ℝ) : ℝ :=
  (8/3 : ℝ)^3*C₀^3*X*Y*Real.log (2*T+2)^3*(∫ u : ℝ, |ω u|)

/-- Full zero-series product, with the third slot conjugated. -/
def tripleMasterProduct (ω : ℝ → ℝ) (T X Y t : ℝ) : ℂ :=
  (ω (t/T)/T : ℝ)*pairZeroSeries (X,t)*pairZeroSeries (Y,t)*
    star (pairZeroSeries (X*Y,t))

def tripleMasterObservable (ω : ℝ → ℝ) (T X Y : ℝ) : ℂ :=
  ∫ t : ℝ, tripleMasterProduct ω T X Y t

def tripleMasterDenominator (i : ZeroOccurrence) (t : ℝ) : ℂ :=
  1 + ((t-occurrenceOrdinate i : ℝ) + Complex.I*occurrenceDisplacement i)^2

def tripleMasterKernelIntegrand (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) (t : ℝ) : ℂ :=
  (ω (t/T)/T : ℝ) /
    (tripleMasterDenominator (v 0) t * tripleMasterDenominator (v 1) t *
      star (tripleMasterDenominator (v 2) t))

/-- Smoothed absolute-center kernel K_T; not the unweighted integral profile. -/
def tripleMasterKernel (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) : ℂ :=
  ∫ t : ℝ, tripleMasterKernelIntegrand ω T v t

/-- Positive-real base powers are exp(log(base) * exponent). -/
def tripleMasterCoefficient (X Y : ℝ) (v : MasterTriple) : ℂ :=
  Complex.exp ((Real.log X : ℂ)*(occurrenceValue (v 0)+star (occurrenceValue (v 2))-1)) *
  Complex.exp ((Real.log Y : ℂ)*(occurrenceValue (v 1)+star (occurrenceValue (v 2))-1))

end
end HigherCorrelations
