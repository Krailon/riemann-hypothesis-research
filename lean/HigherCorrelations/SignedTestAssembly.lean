import HigherCorrelations.SignedIdentity
import HigherCorrelations.SignedSectorMeasure
import HigherCorrelations.SignedFrequencySymmetry
import HigherCorrelations.SignedTestRegularity
import HigherCorrelations.TripleQuadrantAssembly

/-! UNCONDITIONAL exact signed test passage, with full complex zero arguments. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem signedConjugate_integral (j : Fin 6) (f : ℝ × ℝ → ℂ) (μ : Measure (ℝ × ℝ)) :
    signedConjugate j (∫ p, f p ∂μ) = ∫ p, signedConjugate j (f p) ∂μ := by
  unfold signedConjugate
  split_ifs
  · rfl
  · exact integral_conj.symm

theorem signedConjugate_div_real (j : Fin 6) (z : ℂ) (r : ℝ) :
    signedConjugate j (z/(r:ℂ)) = signedConjugate j z/(r:ℂ) := by
  unfold signedConjugate
  split_ifs <;> simp [map_div₀]

theorem signed_normalized_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hκ : 0<κ) (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) :
    signedStatistic ω φ T = (∫ p, φ p*signedFrequency ω T p)/(Real.log T:ℂ) := by
  rw [signedStatistic,signed_identity ω hω φ hφ κ T hκ hT hs]

theorem signed_zero_identity (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) :
    signedStatistic ω φ T = (8/(Real.log T:ℂ))*
      ∑' v : MasterTriple, tripleMasterKernel ω T (tripleTestToMaster v)*
        complexFourier φ (tripleTestArguments T v) := by
  unfold signedStatistic tripleTestStatistic
  ring

theorem signed_independent_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hκ : 0<κ) (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      (8/(Real.log T:ℂ))*∑ v ∈ tripleDomain S,
        tripleMasterKernel ω T (tripleTestToMaster v)*
          complexFourier φ (tripleTestArguments T v)) atTop
      (𝓝 (signedStatistic ω φ T)) := by
  rw [signed_zero_identity]
  exact (triple_cutoff_limit _ (signed_zero_sum_absolute ω hω φ hφ κ T hκ hT hs)).const_mul _

theorem signed_sector_decomposition (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ T : ℝ) (hκ : 0<κ) (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) :
    signedStatistic ω φ T = ∑ j : Fin 6,
      signedConjugate j (tripleQuadrantStatistic ω (signedPullback φ j) T) := by
  have hi := hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hc
  rw [signed_normalized_identity ω hω φ hi κ T hκ hT hs,
    signedSector_partition_integral _ (signed_frequency_integrable ω hω φ hi κ T hκ hT hs),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [tripleQuadrant_normalized_identity ω hω _ (signedPullback_smooth φ hφ j)
    (signedPullback_compact φ hc j) κ T hκ hT (signedPullback_support φ κ hs j),
    signedConjugate_div_real,signedConjugate_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with p
  change φ (signedSector j p)*signedFrequency ω T (signedSector j p)=
    signedConjugate j (signedPullback φ j p*signedFrequency ω T p)
  rw [signedFrequency_sector ω T hT]
  unfold signedPullback signedConjugate
  split_ifs <;> simp [star_mul,mul_comm]

end
end HigherCorrelations
