import HigherCorrelations.TriplePrimeFourierDefinitions

/-! UNCONDITIONAL definition-only arithmetic resonance interface.
Exponents are positive and ordered. Integer-one zero coefficients are retained
in the ambient series. Resonance does not depend on the smoothing weight. -/
namespace HigherCorrelations
noncomputable section

abbrev PrimePowerParameters := {p : ℕ // p.Prime} ×
  ({a : ℕ // 0<a} × {b : ℕ // 0<b})

def primePowerIndex (q : PrimePowerParameters) : PrimeTriple :=
  ![q.1.val^q.2.1.val-1, q.1.val^q.2.2.val-1,
    q.1.val^(q.2.1.val+q.2.2.val)-1]

def triplePrimeResonant (v : PrimeTriple) : Prop :=
  (v 0+1)*(v 1+1) = v 2+1

abbrev SupportedPrimeResonance := {v : PrimeTriple //
  triplePrimeResonant v ∧ ∀ r, IsPrimePow (v r+1)}

def triplePrimeResonantMass (X Y : ℝ) : ℝ :=
  ∑' q : PrimePowerParameters, triplePrimeCoefficient X Y (primePowerIndex q)

def triplePrimeOffSeries (ω : ℝ → ℝ) (T X Y : ℝ) : ℂ :=
  ∑' v : {v : PrimeTriple // ¬triplePrimeResonant v}, triplePrimeFourierTerm ω T X Y v.val

end
end HigherCorrelations
