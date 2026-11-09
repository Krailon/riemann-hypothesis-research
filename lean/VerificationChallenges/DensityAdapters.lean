import HigherCorrelations.DensityCountDefinitions

-- Statement contracts only; Comparator must reject these unfinished bodies.
namespace HigherCorrelations
noncomputable section
open scoped Classical

theorem mem_rightDensityWindow (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ rightDensityWindow a b D ↔
      a < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ D < occurrenceDisplacement i := by sorry

theorem mem_leftDensityWindow (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ leftDensityWindow a b D ↔
      a < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ occurrenceDisplacement i < -D := by sorry

theorem mem_horizontalDensityWindow (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ horizontalDensityWindow a b D ↔
      a < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ D < |occurrenceDisplacement i| := by sorry

theorem mem_rightDensityInterval (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ rightDensityInterval a b D ↔
      a ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ D < occurrenceDisplacement i := by sorry

theorem mem_leftDensityInterval (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ leftDensityInterval a b D ↔
      a ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ occurrenceDisplacement i < -D := by sorry

theorem mem_horizontalDensityInterval (a b D : ℝ) (i : ZeroOccurrence) :
    i ∈ horizontalDensityInterval a b D ↔
      a ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ b ∧ D < |occurrenceDisplacement i| := by sorry

theorem rightDensityWindow_empty (a b D : ℝ) (h : b ≤ a) : rightDensityWindow a b D = ∅ := by sorry

theorem horizontalDensityWindow_empty (a b D : ℝ) (h : b ≤ a) :
    horizontalDensityWindow a b D = ∅ := by sorry

theorem horizontalDensityInterval_empty (a b D : ℝ) (h : b < a) :
    horizontalDensityInterval a b D = ∅ := by sorry

theorem rightDensityWindow_mono {a b D a' b' D' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') (hD : D' ≤ D) :
    rightDensityWindow a b D ⊆ rightDensityWindow a' b' D' := by sorry

theorem horizontalDensityInterval_mono {a b D a' b' D' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') (hD : D' ≤ D) :
    horizontalDensityInterval a b D ⊆ horizontalDensityInterval a' b' D' := by sorry

theorem rightDensityWindow_card (a b D : ℝ) :
    (rightDensityWindow a b D).card =
      ∑ ρ ∈ (stripZeroInterval a b).filter (fun ρ => a < ρ.val.im ∧ D < ρ.val.re-1/2),
        zeroMultiplicity ρ := by sorry

theorem horizontalDensityInterval_card (a b D : ℝ) :
    (horizontalDensityInterval a b D).card =
      ∑ ρ ∈ (stripZeroInterval a b).filter (fun ρ => D < |ρ.val.re-1/2|),
        zeroMultiplicity ρ := by sorry

theorem rightDensityInterval_endpoint (a b D : ℝ) (hab : a ≤ b) :
    (rightDensityInterval a b D).card = (rightDensityWindow a b D).card +
      (rightDensityInterval a a D).card := by sorry

theorem horizontalDensityInterval_endpoint (a b D : ℝ) (hab : a ≤ b) :
    (horizontalDensityInterval a b D).card = (horizontalDensityWindow a b D).card +
      (horizontalDensityInterval a a D).card := by sorry

theorem rightDensityCount_split (σ a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    rightDensityCount σ b = rightDensityCount σ a + (rightDensityWindow a b (σ-1/2)).card := by sorry

theorem rightDensityCount_difference (σ a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    rightDensityCount σ b - rightDensityCount σ a = (rightDensityWindow a b (σ-1/2)).card := by sorry

theorem densityWindow_reflection (a b D : ℝ) :
    (leftDensityWindow a b D).card = (rightDensityWindow a b D).card := by sorry

theorem densityInterval_reflection (a b D : ℝ) :
    (leftDensityInterval a b D).card = (rightDensityInterval a b D).card := by sorry

theorem horizontalDensityWindow_twice_right (a b D : ℝ) (hD : 0 ≤ D) :
    (horizontalDensityWindow a b D).card = 2*(rightDensityWindow a b D).card := by sorry

theorem horizontalDensityInterval_twice_right (a b D : ℝ) (hD : 0 ≤ D) :
    (horizontalDensityInterval a b D).card = 2*(rightDensityInterval a b D).card := by sorry

theorem horizontalDensityInterval_excludes_boundary (a b D : ℝ) (i : ZeroOccurrence)
    (hi : |occurrenceDisplacement i| = D) : i ∉ horizontalDensityInterval a b D := by sorry

theorem horizontalDensityInterval_excludes_line (a b : ℝ) (i : ZeroOccurrence)
    (hi : occurrenceDisplacement i = 0) : i ∉ horizontalDensityInterval a b 0 := by sorry

theorem leftDensityWindow_empty (a b D : ℝ) (h : b ≤ a) : leftDensityWindow a b D = ∅ := by sorry

theorem rightDensityInterval_empty (a b D : ℝ) (h : b < a) : rightDensityInterval a b D = ∅ := by sorry

theorem leftDensityInterval_empty (a b D : ℝ) (h : b < a) : leftDensityInterval a b D = ∅ := by sorry

theorem mem_horizontalDensityInterval_singleton (a D : ℝ) (i : ZeroOccurrence) :
    i ∈ horizontalDensityInterval a a D ↔
      occurrenceOrdinate i = a ∧ D < |occurrenceDisplacement i| := by sorry

theorem rightDensityCount_card (σ V : ℝ) :
    rightDensityCount σ V =
      ∑ ρ ∈ (stripZeroInterval 0 V).filter (fun ρ => 0 < ρ.val.im ∧ σ < ρ.val.re),
        zeroMultiplicity ρ := by sorry

theorem densityInterval_dyadic_cover (T D : ℝ) (hT : 0 < T) :
    (rightDensityInterval (T/2) (5*T/2) D).card ≤
      (rightDensityWindow (T/4) (T/2) D).card +
      (rightDensityWindow (T/2) T D).card +
      (rightDensityWindow T (2*T) D).card +
      (rightDensityWindow (2*T) (4*T) D).card := by sorry

theorem density_comparable_interval (C T₀ T D : ℝ)
    (h : UniformDyadicDensity C T₀) (hT : 4*T₀ ≤ T)
    (hD : 0 ≤ D) (hD' : D ≤ 331/1000) :
    ((horizontalDensityInterval (T/2) (5*T/2) D).card : ℝ) ≤
      32*C*(T^(1-D/4)*Real.log T+(Real.log T)^2) := by sorry

theorem density_power_exp (T v : ℝ) (hT : 1 < T) :
    T^(1-(v/Real.log T)/4) = T*Real.exp (-v/4) := by sorry

theorem density_scaled_tail_bound (C T₀ T v : ℝ)
    (h : UniformDyadicDensity C T₀) (hT : 4*T₀ ≤ T)
    (hv : 0 ≤ v) (hv' : v ≤ (331/1000)*Real.log T) :
    (densityScaledTail T v : ℝ) ≤
      32*C*(T*Real.log T*Real.exp (-v/4)+(Real.log T)^2) := by sorry

theorem density_scaled_tail_antitone (T : ℝ) (hT : 1 < T) :
    Antitone (densityScaledTail T) := by sorry

theorem density_scaled_tail_endpoint (C T₀ T : ℝ)
    (h : UniformDyadicDensity C T₀) (hT : 4*T₀ ≤ T) :
    (densityScaledTail T ((331/1000)*Real.log T) : ℝ) ≤
      32*C*(T^((1:ℝ)-331/4000)*Real.log T+(Real.log T)^2) := by sorry

theorem density_scaled_tail_frozen (C T₀ T v : ℝ)
    (h : UniformDyadicDensity C T₀) (hT : 4*T₀ ≤ T)
    (hv : (331/1000)*Real.log T ≤ v) :
    (densityScaledTail T v : ℝ) ≤
      32*C*(T^((1:ℝ)-331/4000)*Real.log T+(Real.log T)^2) := by sorry

end
end HigherCorrelations
