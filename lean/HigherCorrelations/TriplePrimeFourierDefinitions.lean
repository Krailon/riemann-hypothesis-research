import HigherCorrelations.TripleExpansionDefinitions

/-! UNCONDITIONAL definition-only cubic prime Fourier interface.
An index n denotes the positive integer n+1, including the zero coefficient at 1.
The third slot is conjugated. No probability normalization of omega is assumed. -/
namespace HigherCorrelations
noncomputable section

abbrev PrimeTriple := Fin 3 → ℕ

def triplePrimeMass (X : ℝ) : ℝ := ∑' n, pairMeanPrimeCoefficient X n

def triplePrimeCoefficient (X Y : ℝ) (v : PrimeTriple) : ℝ :=
  pairMeanPrimeCoefficient X (v 0)*pairMeanPrimeCoefficient Y (v 1)*
    pairMeanPrimeCoefficient (X*Y) (v 2)

def triplePrimeFrequency (T : ℝ) (v : PrimeTriple) : ℝ :=
  T/(2*Real.pi)*Real.log (((v 0+1:ℕ):ℝ)*((v 1+1:ℕ):ℝ)/((v 2+1:ℕ):ℝ))

def triplePrimeTerm (ω : ℝ → ℝ) (T X Y : ℝ) (v : PrimeTriple) (t : ℝ) : ℂ :=
  (ω (t/T)/T : ℝ)*pairPrimeTerm (v 0) (X,t)*pairPrimeTerm (v 1) (Y,t)*
    star (pairPrimeTerm (v 2) (X*Y,t))

def triplePrimeFourierTerm (ω : ℝ → ℝ) (T X Y : ℝ) (v : PrimeTriple) : ℂ :=
  (triplePrimeCoefficient X Y v:ℂ)*pairMeanFourier (fun u => (ω u:ℂ)) (triplePrimeFrequency T v)

def triplePrimeL1Bound (ω : ℝ → ℝ) (X Y : ℝ) : ℝ :=
  triplePrimeMass X*triplePrimeMass Y*triplePrimeMass (X*Y)*(∫ u : ℝ, |ω u|)

end
end HigherCorrelations
