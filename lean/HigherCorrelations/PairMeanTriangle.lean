import HigherCorrelations.PairMeanFourier
import HigherCorrelations.PairMeanKernelBounds

/-! UNCONDITIONAL box convolution and the squared-sinc transform.
The Fourier sign is negative and frequencies are in cycles. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex
open scoped FourierTransform Convolution

theorem pairMeanBox_convolution (ξ : ℝ) :
    (pairMeanBox ⋆[ContinuousLinearMap.mul ℂ ℂ] pairMeanBox) ξ =
      (pairMeanTriangle ξ : ℂ) := by
  rw [convolution_def]
  have he : (fun t : ℝ => (ContinuousLinearMap.mul ℂ ℂ)
      (pairMeanBox t) (pairMeanBox (ξ-t))) =
      Set.indicator (Set.Icc (max (-(1/2:ℝ)) (ξ-1/2)) (min (1/2) (ξ+1/2)))
        (fun _ : ℝ => (1:ℂ)) := by
    funext t
    simp only [ContinuousLinearMap.mul_apply', pairMeanBox]
    by_cases h1 : t ∈ Set.Icc (-(1/2:ℝ)) (1/2)
    · by_cases h2 : ξ-t ∈ Set.Icc (-(1/2:ℝ)) (1/2)
      · have h3 : t ∈ Set.Icc (max (-(1/2:ℝ)) (ξ-1/2)) (min (1/2) (ξ+1/2)) := by
          simp only [Set.mem_Icc, max_le_iff, le_min_iff] at *
          constructor <;> constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
        rw [Set.indicator_of_mem h1,Set.indicator_of_mem h2,Set.indicator_of_mem h3,mul_one]
      · have h3 : t ∉ Set.Icc (max (-(1/2:ℝ)) (ξ-1/2)) (min (1/2) (ξ+1/2)) := by
          intro h3
          apply h2
          simp only [Set.mem_Icc, max_le_iff, le_min_iff] at *
          constructor <;> linarith [h3.1.1,h3.1.2,h3.2.1,h3.2.2]
        rw [Set.indicator_of_notMem h2,Set.indicator_of_notMem h3,mul_zero]
    · have h3 : t ∉ Set.Icc (max (-(1/2:ℝ)) (ξ-1/2)) (min (1/2) (ξ+1/2)) := by
        intro h3
        apply h1
        simp only [Set.mem_Icc,max_le_iff,le_min_iff] at *
        exact ⟨h3.1.1,h3.2.1⟩
      rw [Set.indicator_of_notMem h1,Set.indicator_of_notMem h3,zero_mul]
  rw [he, integral_indicator_const 1 measurableSet_Icc, Real.volume_real_Icc]
  simp only [Complex.real_smul, mul_one]
  congr 1
  unfold pairMeanTriangle
  by_cases hξ : 0 ≤ ξ
  · rw [abs_of_nonneg hξ, max_eq_right (by linarith : -(1/2:ℝ) ≤ ξ-1/2),
      min_eq_left (by linarith : (1/2:ℝ) ≤ ξ+1/2)]
    rw [max_comm]
    congr 1 <;> ring
  · have hn := le_of_not_ge hξ
    rw [abs_of_nonpos hn, max_eq_left (by linarith : ξ-1/2 ≤ -(1/2:ℝ)),
      min_eq_right (by linarith : ξ+1/2 ≤ (1/2:ℝ))]
    rw [max_comm]
    congr 1 <;> ring

theorem pairMeanTriangle_continuous : Continuous pairMeanTriangle := by
  unfold pairMeanTriangle
  fun_prop

theorem pairMeanTriangle_eq_zero (ξ : ℝ) (hξ : 1 ≤ |ξ|) : pairMeanTriangle ξ = 0 := by
  exact max_eq_left (by linarith)

theorem pairMeanTriangle_compactSupport : HasCompactSupport pairMeanTriangle := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))
  intro ξ hξ
  apply pairMeanTriangle_eq_zero
  simp only [Set.mem_Icc, not_and_or, not_le] at hξ
  rcases hξ with hξ | hξ
  · exact (by linarith : (1:ℝ) ≤ -ξ).trans (neg_le_abs ξ)
  · exact (le_of_lt hξ).trans (le_abs_self ξ)

theorem pairMeanTriangle_integrable : Integrable pairMeanTriangle :=
  pairMeanTriangle_continuous.integrable_of_hasCompactSupport pairMeanTriangle_compactSupport

theorem pairMeanTriangle_fourier (ξ : ℝ) :
    pairMeanFourier (fun t => (pairMeanTriangle t:ℂ)) ξ = (pairMeanSinc ξ:ℂ)^2 := by
  rw [pairMeanFourier_eq]
  have he : (fun t => (pairMeanTriangle t:ℂ)) =
      pairMeanBox ⋆[ContinuousLinearMap.mul ℂ ℂ] pairMeanBox :=
    funext fun t => (pairMeanBox_convolution t).symm
  rw [he, Real.fourier_mul_convolution_eq pairMeanBox_integrable pairMeanBox_integrable,
    ← pairMeanFourier_eq, pairMeanBox_fourier, pow_two]

theorem pairMeanSinc_sq_fourier (ξ : ℝ) :
    pairMeanFourier (fun t => ((pairMeanSinc t)^2:ℂ)) ξ = (pairMeanTriangle ξ:ℂ) := by
  have hf : Integrable (fun t => (pairMeanTriangle t:ℂ)) := pairMeanTriangle_integrable.ofReal
  have ht : 𝓕 (fun t => (pairMeanTriangle t:ℂ)) = fun t => ((pairMeanSinc t)^2:ℂ) := by
    funext t
    rw [← pairMeanFourier_eq, pairMeanTriangle_fourier]
  have hft : Integrable (𝓕 (fun t => (pairMeanTriangle t:ℂ))) := by
    rw [ht]
    have hh : Integrable (fun t : ℝ => (↑(pairMeanSinc t^2):ℂ)) :=
      pairMeanSinc_sq_integrable.ofReal
    convert hh using 1
    funext t
    push_cast
    rfl
  have hv := hf.fourierInv_fourier_eq hft
    (Complex.continuous_ofReal.comp pairMeanTriangle_continuous).continuousAt (v := -ξ)
  rw [Real.fourierInv_eq_fourier_neg, ht, neg_neg, ← pairMeanFourier_eq] at hv
  simpa only [pairMeanTriangle, abs_neg] using hv

end
end HigherCorrelations
