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

end
end HigherCorrelations
