import HigherCorrelations.OccurrenceLimits
import HigherCorrelations.HorizontalSquare

/-! UNCONDITIONAL integration implications. Evaluated-integral summability and
summability of integral norms are deliberately separate interfaces.
-/
namespace HigherCorrelations
open Filter MeasureTheory
open scoped Topology

theorem evaluated_integrals_summable {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : I → X → ℂ) (_hG : ∀ i, Integrable (G i) μ)
    (B : I → ℝ) (hB : Summable B) (hbound : ∀ i, ‖∫ x, G i x ∂μ‖ ≤ B i) :
    Summable (fun i => ‖∫ x, G i x ∂μ‖) := by
  apply hB.of_norm_bounded
  intro i
  simpa only [norm_norm] using hbound i

theorem evaluated_integrals_cutoff_limit {I K X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : I → X → ℂ) (hG : ∀ i, Integrable (G i) μ)
    (B : I → ℝ) (hB : Summable B) (hbound : ∀ i, ‖∫ x, G i x ∂μ‖ ≤ B i)
    (l : Filter K) (S : K → Finset I) (hS : ∀ i, ∀ᶠ k in l, i ∈ S k) :
    Tendsto (fun k => ∑ i ∈ S k, ∫ x, G i x ∂μ) l
      (𝓝 (∑' i, ∫ x, G i x ∂μ)) :=
  occurrence_cutoff_limit l S hS _ (evaluated_integrals_summable μ G hG B hB hbound)

theorem integral_occurrence_sum {I X : Type*} [Countable I] [MeasurableSpace X]
    (μ : Measure X) (G : I → X → ℂ) (hG : ∀ i, Integrable (G i) μ)
    (hL1 : Summable (fun i => ∫ x, ‖G i x‖ ∂μ)) :
    (∑' i, ∫ x, G i x ∂μ) = ∫ x, ∑' i, G i x ∂μ :=
  integral_tsum_of_summable_integral_norm hG hL1

theorem integral_occurrence_cutoff_limit {I K X : Type*}
    [Countable I] [MeasurableSpace X] (μ : Measure X) (G : I → X → ℂ)
    (hG : ∀ i, Integrable (G i) μ)
    (hL1 : Summable (fun i => ∫ x, ‖G i x‖ ∂μ))
    (l : Filter K) (S : K → Finset I) (hS : ∀ i, ∀ᶠ k in l, i ∈ S k) :
    Tendsto (fun k => ∫ x, ∑ i ∈ S k, G i x ∂μ) l
      (𝓝 (∫ x, ∑' i, G i x ∂μ)) := by
  have h := evaluated_integrals_cutoff_limit μ G hG _ hL1
    (fun i => norm_integral_le_integral_norm _) l S hS
  rw [integral_occurrence_sum μ G hG hL1] at h
  simpa only [integral_finsetSum _ (fun i _ => hG i)] using h

theorem dominated_integral_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : ℕ → X → ℂ) (g : X → ℂ) (B : X → ℝ)
    (hG : ∀ n, AEStronglyMeasurable (G n) μ) (hB : Integrable B μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖G n x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) :=
  tendsto_integral_of_dominated_convergence B hG hB hbound hlim

theorem continuous_cosh_excess {I : Type*} (D : Finset I) (δ : I → ℝ) (b : ℝ) :
    Continuous (fun z : ℝ × ℝ => sameOrdinateCoshSum D δ b z.1 z.2) := by
  unfold sameOrdinateCoshSum horizontalCoshExcess
  fun_prop

theorem continuous_frequency_form :
    Continuous (fun z : ℝ × ℝ => horizontalFrequencyForm z.1 z.2) := by
  unfold horizontalFrequencyForm
  fun_prop

theorem integrable_weighted_cosh {I : Type*} (D : Finset I) (δ : I → ℝ) (b : ℝ)
    (φ : ℝ × ℝ → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => φ z * sameOrdinateCoshSum D δ b z.1 z.2) :=
  (hφ.mul (continuous_cosh_excess D δ b)).integrable_of_hasCompactSupport hc.mul_right

theorem integrable_weighted_frequency (φ : ℝ × ℝ → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => φ z * horizontalFrequencyForm z.1 z.2) :=
  (hφ.mul continuous_frequency_form).integrable_of_hasCompactSupport hc.mul_right

theorem integrated_frequency_nonneg (φ : ℝ × ℝ → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    0 ≤ integratedFrequencyForm φ :=
  integral_nonneg (fun z => mul_nonneg (hφ z) (horizontal_frequency_nonneg z.1 z.2))

theorem integrated_cosh_nonneg {I : Type*} (D : Finset I) (δ : I → ℝ) (b : ℝ)
    (φ : ℝ × ℝ → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    0 ≤ integratedCoshExcess D δ b φ :=
  integral_nonneg (fun z => mul_nonneg (hφ z) (same_ordinate_cosh_nonneg D δ b z.1 z.2))

theorem integrated_horizontal_square_lower {I : Type*}
    (D : Finset I) (δ : I → ℝ) (b : ℝ) (φ : ℝ × ℝ → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hn : ∀ z, 0 ≤ φ z) :
    b ^ 2 * (D.card : ℝ) ^ 2 * horizontalSquareMass D δ * integratedFrequencyForm φ ≤
      integratedCoshExcess D δ b φ := by
  unfold integratedFrequencyForm integratedCoshExcess
  rw [← integral_const_mul]
  apply integral_mono
    ((integrable_weighted_frequency φ hφ hc).const_mul _)
    (integrable_weighted_cosh D δ b φ hφ hc)
  intro z
  have h := mul_le_mul_of_nonneg_left
    (same_ordinate_horizontal_square_lower D δ b z.1 z.2) (hn z)
  convert h using 1; ring

theorem integrated_fibers_lower {I G : Type*} [Countable G]
    (D : G → Finset I) (δ : I → ℝ) (W : G → ℝ) (hW : ∀ g, 0 ≤ W g)
    (b : ℝ) (φ : ℝ × ℝ → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hn : ∀ z, 0 ≤ φ z)
    (hs : Summable (fun g => W g * integratedCoshExcess (D g) δ b φ)) :
    Summable (fun g => W g * (b ^ 2 * ((D g).card : ℝ) ^ 2 *
      horizontalSquareMass (D g) δ * integratedFrequencyForm φ)) ∧
    (∑' g, W g * (b ^ 2 * ((D g).card : ℝ) ^ 2 *
      horizontalSquareMass (D g) δ * integratedFrequencyForm φ)) ≤
      ∑' g, W g * integratedCoshExcess (D g) δ b φ := by
  have hnon (g : G) : 0 ≤ W g * (b ^ 2 * ((D g).card : ℝ) ^ 2 *
      horizontalSquareMass (D g) δ * integratedFrequencyForm φ) := by
    have hQ := horizontal_square_mass_nonneg (D g) δ
    have hP := integrated_frequency_nonneg φ hn
    have hw := hW g
    positivity
  have hle (g : G) := mul_le_mul_of_nonneg_left
    (integrated_horizontal_square_lower (D g) δ b φ hφ hc hn) (hW g)
  have hl := hs.of_nonneg_of_le hnon hle
  exact ⟨hl, hl.tsum_le_tsum hle hs⟩

end HigherCorrelations
