import HigherCorrelations.PairFourierDefinitions
import HigherCorrelations.PairNormalizedSymmetry
import HigherCorrelations.PairMeanFourier

/-! UNCONDITIONAL exact finite-pair Fourier identity. Compact support supplies
integrability at genuinely complex arguments; only finite sums are interchanged. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped FourierTransform

theorem pairComplexFourier_integrable (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (z : ℂ) :
    Integrable (fun a : ℝ => g a*Complex.exp (-2*Real.pi*Complex.I*z*a)) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right

theorem pairComplexFourier_real (g : ℝ → ℂ) (x : ℝ) :
    pairComplexFourier g x = 𝓕 g x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold pairComplexFourier
  congr 1; funext a
  simp only [smul_eq_mul]
  rw [mul_comm (g a)]
  congr 2
  push_cast
  ring

theorem pairComplexFourier_zero_argument (g : ℝ → ℂ) :
    pairComplexFourier g 0 = ∫ a : ℝ, g a := by
  simp [pairComplexFourier]

theorem pairComplexFourier_argument (g : ℝ → ℂ) (T : ℝ) (z : ℂ) :
    pairComplexFourier g (Complex.I*pairSourceSpacing T*z) =
      ∫ a : ℝ, g a*Complex.exp ((a*Real.log T : ℝ)*z) := by
  unfold pairComplexFourier pairSourceSpacing
  congr 1; funext a
  congr 2
  push_cast
  field_simp
  simp [Complex.I_sq]

theorem pairFrequencyTerm_sum (T a : ℝ) (hT : 0<T) :
    (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T, pairFrequencyTerm T a i j) =
      pairCorrelationSum (T^a) T := by
  simp only [pairFrequencyTerm,pairDifferenceWeight,pairCorrelationSum,Real.log_rpow hT]

theorem pairFrequencyTerm_continuous (T : ℝ) (i j : ZeroOccurrence) :
    Continuous (fun a => pairFrequencyTerm T a i j) := by
  unfold pairFrequencyTerm
  fun_prop

theorem pairNormalizedCorrelation_continuous (T : ℝ) (hT : 0<T) :
    Continuous (pairNormalizedCorrelation T) := by
  have he (a : ℝ) : pairNormalizedCorrelation T a =
      2*Real.pi*(∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
        pairFrequencyTerm T a i j).re/(T*Real.log T) := by
    rw [pairFrequencyTerm_sum T a hT]; rfl
  change Continuous (fun a => pairNormalizedCorrelation T a)
  simp_rw [he]
  exact ((continuous_const.mul (Complex.continuous_re.comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => pairFrequencyTerm_continuous T i j))).div_const _)

theorem pairFourierStatistic_integrable (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (T : ℝ) (hT : 0<T) :
    Integrable (fun a => g a*(pairNormalizedCorrelation T a : ℂ)) :=
  (hg.mul (Complex.continuous_ofReal.comp (pairNormalizedCorrelation_continuous T hT))).integrable_of_hasCompactSupport hc.mul_right

theorem pairFourierStatistic_identity (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (T : ℝ) (hT : 3≤T) :
    pairFourierStatistic T g = ∫ a : ℝ, g a*(pairNormalizedCorrelation T a : ℂ) := by
  classical
  have ht : 0<T := by linarith
  have hi (i j : ZeroOccurrence) : Integrable (fun a => g a*pairFrequencyTerm T a i j) :=
    (hg.mul (pairFrequencyTerm_continuous T i j)).integrable_of_hasCompactSupport hc.mul_right
  have hn (a : ℝ) : g a*(pairNormalizedCorrelation T a : ℂ) =
      (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
        g a*pairFrequencyTerm T a i j)/(pairNormalization T : ℂ) := by
    rw [pairNormalizedCorrelation_complex T a hT,← pairFrequencyTerm_sum T a ht]
    simp only [pairNormalization,← mul_div_assoc,Finset.mul_sum]
  simp_rw [hn]
  rw [integral_div,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  unfold pairFourierStatistic
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  apply Finset.sum_congr rfl
  intro j hj'
  rw [pairComplexFourier_argument,← integral_const_mul]
  congr 1; funext a
  unfold pairFrequencyTerm
  ring

end
end HigherCorrelations
