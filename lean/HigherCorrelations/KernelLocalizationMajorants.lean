import HigherCorrelations.KernelLocalizationRegions
import HigherCorrelations.KernelLocalizationCounting
import HigherCorrelations.PairZeroMajorants

/-! UNCONDITIONAL finite rectangular domination. Finite sums are bounded before
any infinite sum is taken; no positivity of the complex kernel is assumed. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped NNReal

theorem localizationAnchorWeight_nonneg (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T t : ℝ) (i : ZeroOccurrence) : 0≤localizationAnchorWeight r ω T t i :=
  Set.indicator_nonneg (fun u _ => mul_nonneg (ordinateKernel_nonneg _) (abs_nonneg _)) t

theorem localizationRegionalDensity_majorant (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (hT : 0<T) (v : MasterTriple) (t : ℝ) :
    ‖localizationRegionalDensity r ω T v t‖ ≤ (64/(27*T)) *
      (ordinateKernel (t-occurrenceOrdinate (v 0))*ordinateKernel (t-occurrenceOrdinate (v 1))*
        localizationAnchorWeight r ω T t (v 2)) := by
  classical
  by_cases ht : t ∈ localizationRegionSet r T (occurrenceOrdinate (v 2))
  · simp only [localizationRegionalDensity, localizationAnchorWeight, Set.indicator_of_mem ht]
    have h₁ := scalarKernel_half_strip_bound (t-occurrenceOrdinate (v 0))
      (occurrenceDisplacement (v 0)) (occurrence_displacement_lt (v 0)).le
    have h₂ := scalarKernel_half_strip_bound (t-occurrenceOrdinate (v 1))
      (occurrenceDisplacement (v 1)) (occurrence_displacement_lt (v 1)).le
    have h₃ := scalarKernel_half_strip_bound (t-occurrenceOrdinate (v 2))
      (-occurrenceDisplacement (v 2)) (by simpa using (occurrence_displacement_lt (v 2)).le)
    have hh := mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)) h₃ (norm_nonneg _) (by positivity)
    have he (a b : ℝ) : t-a-(b-a)=t-b := by ring
    simp only [localizationErrorDensity, tripleKernelLocalizationIntegrand,
      tripleAnchoredProfileIntegrand, profileIntegrand, he, add_sub_cancel,
      norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    calc
      _ ≤ (1/T)*|ω (t/T)-ω (occurrenceOrdinate (v 2)/T)| *
        (((4/3)/(1+(t-occurrenceOrdinate (v 0))^2))*
          ((4/3)/(1+(t-occurrenceOrdinate (v 1))^2))*
          ((4/3)/(1+(t-occurrenceOrdinate (v 2))^2))) := by
        nlinarith [mul_le_mul_of_nonneg_left hh
          (show 0≤(1/T)*|ω (t/T)-ω (occurrenceOrdinate (v 2)/T)| by positivity)]
      _ = _ := by unfold ordinateKernel; ring
  · simp [localizationRegionalDensity, localizationAnchorWeight, ht]

theorem localization_finite_product (D : Finset MasterTriple) (s : Finset ZeroOccurrence)
    (hs : ∀ v ∈ D, ∀ r, v r ∈ s) (t : ℝ) (f : ZeroOccurrence → ℝ) (hf : ∀ i, 0≤f i) :
    (∑ v ∈ D, ordinateKernel (t-occurrenceOrdinate (v 0))*
      ordinateKernel (t-occurrenceOrdinate (v 1))*f (v 2)) ≤
      (zeroKernelSum t)^2*(∑ i ∈ s, f i) := by
  classical
  let g : Fin 3 → ZeroOccurrence → ℝ := ![fun i => ordinateKernel (t-occurrenceOrdinate i),
    fun i => ordinateKernel (t-occurrenceOrdinate i), f]
  have hsub : D ⊆ Fintype.piFinset (fun _ : Fin 3 => s) := by
    intro v hv
    exact Fintype.mem_piFinset.mpr (hs v hv)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun v => ordinateKernel (t-occurrenceOrdinate (v 0))*
      ordinateKernel (t-occurrenceOrdinate (v 1))*f (v 2))
    (fun v _ _ => mul_nonneg (mul_nonneg (ordinateKernel_nonneg _) (ordinateKernel_nonneg _)) (hf _))
  have he : (∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => s),
      ordinateKernel (t-occurrenceOrdinate (v 0))*ordinateKernel (t-occurrenceOrdinate (v 1))*f (v 2)) =
      (∑ i ∈ s, ordinateKernel (t-occurrenceOrdinate i))^2*(∑ i ∈ s, f i) := by
    have h := Finset.prod_univ_sum (fun _ : Fin 3 => s) g
    simpa [g,Fin.prod_univ_three,pow_two] using h.symm
  rw [he] at hsum
  have hq := (zeroKernel_summable_bound.choose_spec.2 t).1.sum_le_tsum s
    (fun i _ => ordinateKernel_nonneg _)
  exact hsum.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => ordinateKernel_nonneg _)) hq 2)
    (Finset.sum_nonneg (fun i _ => hf i)))

theorem localization_finite_majorant (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (hT : 0<T) (D : Finset MasterTriple) (s : Finset ZeroOccurrence)
    (hs : ∀ v ∈ D, ∀ r, v r ∈ s) (t : ℝ) :
    (∑ v ∈ D, ‖localizationRegionalDensity r ω T v t‖) ≤
      (64/(27*T))*(zeroKernelSum t)^2*(∑ i ∈ s, localizationAnchorWeight r ω T t i) := by
  calc
    _ ≤ ∑ v ∈ D, (64/(27*T))*(ordinateKernel (t-occurrenceOrdinate (v 0))*
        ordinateKernel (t-occurrenceOrdinate (v 1))*localizationAnchorWeight r ω T t (v 2)) :=
      Finset.sum_le_sum (fun v _ => localizationRegionalDensity_majorant r ω T hT v t)
    _ = (64/(27*T))*(∑ v ∈ D, ordinateKernel (t-occurrenceOrdinate (v 0))*
        ordinateKernel (t-occurrenceOrdinate (v 1))*localizationAnchorWeight r ω T t (v 2)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (64/(27*T))*((zeroKernelSum t)^2*(∑ i ∈ s, localizationAnchorWeight r ω T t i)) :=
      mul_le_mul_of_nonneg_left (localization_finite_product D s hs t _
        (localizationAnchorWeight_nonneg r ω T t)) (by positivity)
    _ = _ := by ring

end
end HigherCorrelations
