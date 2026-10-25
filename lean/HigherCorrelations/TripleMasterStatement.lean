import HigherCorrelations.TriplePrimeResonanceDefinitions
import HigherCorrelations.TripleMasterPatternDefinitions
import HigherCorrelations.FourierDecayDefinitions

/-! UNCONDITIONAL definition-only statement of the assembled exact master theorem.
The real C₀ is supplied explicitly; this interface makes no numerical-effectivity claim.
All zero indices denote actual occurrences, retaining both signs and multiplicity. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

structure TripleMasterStatement (C₀ : ℝ) (ω : ℝ → ℝ) (T X Y : ℝ) : Prop where
  integral_norm_summable : Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖)
  integral_norm_bound : (∑' v : MasterTriple, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ≤
    tripleMasterL1Bound C₀ ω T X Y
  sum_integral : (∑' v : MasterTriple, ∫ t : ℝ, tripleMasterTerm ω T X Y v t) =
    ∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω T X Y v t
  kernel_absolute : Summable (fun v : MasterTriple =>
    ‖tripleMasterCoefficient X Y v * tripleMasterKernel ω T v‖)
  kernel_identity : tripleMasterObservable ω T X Y = 8 * ∑' v : MasterTriple,
    tripleMasterCoefficient X Y v * tripleMasterKernel ω T v
  pattern_absolute : ∀ p : TriplePattern, Summable (fun v : MasterPatternTriple p =>
    ‖tripleMasterKernelTerm ω T X Y v.val‖)
  pattern_decomposition : tripleMasterObservable ω T X Y =
    ∑ p : TriplePattern, tripleMasterPatternSeries ω T X Y p
  five_subseries : tripleMasterObservable ω T X Y =
    (∑' i : ZeroOccurrence, tripleMasterKernelTerm ω T X Y ![i,i,i]) +
    (∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.1,q.val.2]) +
    (∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.1]) +
    (∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.2]) +
    (∑' v : MasterDistinctTriple, tripleMasterKernelTerm ω T X Y v.val)
  symmetry : tripleMasterObservable ω T X Y = tripleMasterObservable ω T Y X
  observable_bound : ‖tripleMasterObservable ω T X Y‖ ≤ tripleMasterL1Bound C₀ ω T X Y
  word_expansion : tripleMasterObservable ω T X Y =
    ∑ w : MasterWord, (tripleWordSign w:ℂ)*tripleWordIntegral ω T X Y w
  word_table : tripleMasterObservable ω T X Y =
    (tripleWordTable.map (fun row => (row.2.1:ℂ)*tripleWordIntegral ω T X Y row.1)).sum
  word_count : Fintype.card MasterWord = 27
  prime_absolute : Summable (fun v : PrimeTriple => ‖triplePrimeFourierTerm ω T X Y v‖)
  prime_identity : tripleWordIntegral ω T X Y ![.P,.P,.P] =
    ∑' v : PrimeTriple, triplePrimeFourierTerm ω T X Y v
  resonant_absolute : Summable (fun v : {v : PrimeTriple // triplePrimeResonant v} =>
    ‖triplePrimeFourierTerm ω T X Y v.val‖)
  off_absolute : Summable (fun v : {v : PrimeTriple // ¬triplePrimeResonant v} =>
    ‖triplePrimeFourierTerm ω T X Y v.val‖)
  resonance_classification : ∀ v : PrimeTriple,
    (triplePrimeResonant v ∧ triplePrimeCoefficient X Y v ≠ 0) ↔
      ∃! q : PrimePowerParameters, primePowerIndex q = v
  resonance_mass_absolute : Summable (fun q : PrimePowerParameters =>
    ‖triplePrimeCoefficient X Y (primePowerIndex q)‖)
  resonance_nested : triplePrimeResonantMass X Y =
    ∑' p : {p : ℕ // p.Prime}, ∑' a : {a : ℕ // 0<a}, ∑' b : {b : ℕ // 0<b},
      triplePrimeCoefficient X Y (primePowerIndex (p,a,b))
  resonance_value : (∑' v : {v : PrimeTriple // triplePrimeResonant v},
    triplePrimeFourierTerm ω T X Y v.val) =
      (∫ u : ℝ, (ω u:ℂ))*(triplePrimeResonantMass X Y:ℂ)
  prime_split : tripleWordIntegral ω T X Y ![.P,.P,.P] =
    (∫ u : ℝ, (ω u:ℂ))*(triplePrimeResonantMass X Y:ℂ)+triplePrimeOffSeries ω T X Y
  signed_PPP : (tripleWordSign ![.P,.P,.P]:ℂ)*tripleWordIntegral ω T X Y ![.P,.P,.P] =
    -(∫ u : ℝ, (ω u:ℂ))*(triplePrimeResonantMass X Y:ℂ)-triplePrimeOffSeries ω T X Y
  fourier_mass : ∀ ξ : ℝ, ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤ fourierDerivativeL1 ω 0
  fourier_decay : ∀ (N : ℕ) (ξ : ℝ), ξ≠0 →
    ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤ fourierDerivativeL1 ω N/(2*Real.pi*|ξ|)^N

end
end HigherCorrelations
