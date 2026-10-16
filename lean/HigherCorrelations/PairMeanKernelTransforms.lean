import HigherCorrelations.PairMeanTriangle
import HigherCorrelations.PairMeanFourierRules

/-! UNCONDITIONAL transforms of the smoothing and boundary kernels. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex
open scoped FourierTransform Convolution

theorem pairMeanConvolution_complex (f g : ℝ → ℝ) (t : ℝ) :
    (pairMeanConvolution f g t : ℂ) =
      ((fun t => (f t:ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t => (g t:ℂ))) t := by
  simp only [pairMeanConvolution, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal]
  congr 1
  funext u
  push_cast
  rfl

theorem pairMeanConvolution_integrable (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (pairMeanConvolution f g) := by
  exact hf.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hg

theorem pairMeanTriangle_convolution_continuous :
    Continuous (pairMeanConvolution pairMeanTriangle pairMeanTriangle) :=
  pairMeanTriangle_compactSupport.continuous_convolution_right
    (L := ContinuousLinearMap.mul ℝ ℝ) pairMeanTriangle_integrable.locallyIntegrable
      pairMeanTriangle_continuous

theorem pairMeanTriangle_convolution_fourier (ξ : ℝ) :
    pairMeanFourier (fun t => (pairMeanConvolution pairMeanTriangle pairMeanTriangle t:ℂ)) ξ =
      (pairMeanSinc ξ:ℂ)^4 := by
  have he : (fun t => (pairMeanConvolution pairMeanTriangle pairMeanTriangle t:ℂ)) =
      ((fun t => (pairMeanTriangle t:ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun t => (pairMeanTriangle t:ℂ))) := funext (pairMeanConvolution_complex _ _)
  rw [he, pairMeanFourier_eq, Real.fourier_mul_convolution_eq
    (show Integrable (fun t : ℝ => (pairMeanTriangle t:ℂ)) from pairMeanTriangle_integrable.ofReal)
    (show Integrable (fun t : ℝ => (pairMeanTriangle t:ℂ)) from pairMeanTriangle_integrable.ofReal),
    ← pairMeanFourier_eq, pairMeanTriangle_fourier]
  ring

theorem pairMeanSinc_fourth_integrable : Integrable (fun t : ℝ => pairMeanSinc t^4) := by
  apply pairMeanSinc_sq_integrable.mono' (pairMeanSinc_continuous.pow 4).aestronglyMeasurable
  filter_upwards [] with t
  change ‖pairMeanSinc t^4‖ ≤ pairMeanSinc t^2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := mul_self_le_mul_self (abs_nonneg _) (pairMeanSinc_abs_le_one t)
  have h2 : pairMeanSinc t^2 ≤ 1 := by nlinarith [sq_abs (pairMeanSinc t)]
  nlinarith [sq_nonneg (pairMeanSinc t), mul_self_le_mul_self (sq_nonneg _) h2]

theorem pairMeanTriangle_convolution_even (ξ : ℝ) :
    pairMeanConvolution pairMeanTriangle pairMeanTriangle (-ξ) =
      pairMeanConvolution pairMeanTriangle pairMeanTriangle ξ := by
  unfold pairMeanConvolution
  have he : (fun u => pairMeanTriangle u*pairMeanTriangle (-ξ-u)) =
      fun u => (fun v => pairMeanTriangle v*pairMeanTriangle (ξ-v)) (-u) := by
    funext u
    dsimp only
    simp only [pairMeanTriangle, abs_neg]
    congr 2
    rw [show -ξ-u = -(ξ- -u) by ring, abs_neg]
  rw [he]
  exact integral_neg_eq_self (fun v => pairMeanTriangle v*pairMeanTriangle (ξ-v)) volume

theorem pairMeanSinc_fourth_fourier (ξ : ℝ) :
    pairMeanFourier (fun t => ((pairMeanSinc t)^4:ℂ)) ξ =
      (pairMeanConvolution pairMeanTriangle pairMeanTriangle ξ:ℂ) := by
  have hf : Integrable (fun t => (pairMeanConvolution pairMeanTriangle pairMeanTriangle t:ℂ)) :=
    (pairMeanConvolution_integrable _ _ pairMeanTriangle_integrable pairMeanTriangle_integrable).ofReal
  have ht : 𝓕 (fun t => (pairMeanConvolution pairMeanTriangle pairMeanTriangle t:ℂ)) =
      fun t => ((pairMeanSinc t)^4:ℂ) := by
    funext t
    rw [← pairMeanFourier_eq, pairMeanTriangle_convolution_fourier]
  have hft : Integrable (𝓕 (fun t => (pairMeanConvolution pairMeanTriangle pairMeanTriangle t:ℂ))) := by
    rw [ht]
    have hh : Integrable (fun t : ℝ => (↑(pairMeanSinc t^4):ℂ)) := pairMeanSinc_fourth_integrable.ofReal
    convert hh using 1
    funext t
    push_cast
    rfl
  have hv := hf.fourierInv_fourier_eq hft
    (Complex.continuous_ofReal.comp pairMeanTriangle_convolution_continuous).continuousAt (v := -ξ)
  rw [Real.fourierInv_eq_fourier_neg, ht, neg_neg, ← pairMeanFourier_eq,
    pairMeanTriangle_convolution_even] at hv
  exact hv

theorem pairMeanK_fourier (ξ : ℝ) :
    pairMeanFourier (fun t => (pairMeanK t:ℂ)) ξ =
      (3/2:ℂ)*(pairMeanConvolution pairMeanTriangle pairMeanTriangle (2*ξ):ℂ) := by
  have he : (fun t => (pairMeanK t:ℂ)) =
      fun t => (3/4:ℂ)*(pairMeanSinc (t/2):ℂ)^4 := by
    funext t
    simp only [pairMeanK]
    push_cast
    rfl
  rw [he, pairMeanFourier_const_mul, pairMeanFourier_div (fun t : ℝ => (pairMeanSinc t:ℂ)^4) 2 ξ (by norm_num),
    pairMeanSinc_fourth_fourier]
  norm_num
  ring

theorem pairMeanB_fourier (ξ : ℝ) :
    pairMeanFourier (fun t => (pairMeanB t:ℂ)) ξ =
      2*(1+pairMeanCharacter (-ξ))*(pairMeanTriangle (2*ξ):ℂ) := by
  have hs : Integrable (fun t : ℝ => (pairMeanSinc (t/2):ℂ)^2) := by
    have hh : Integrable (fun t : ℝ => (↑(pairMeanSinc (t/2)^2):ℂ)) :=
      (pairMeanSinc_sq_integrable.comp_div (by norm_num : (2:ℝ) ≠ 0)).ofReal
    convert hh using 1
    funext t
    push_cast
    rfl
  have he : (fun t => (pairMeanB t:ℂ)) =
      fun t => (pairMeanSinc (t/2):ℂ)^2+(pairMeanSinc ((t-1)/2):ℂ)^2 := by
    funext t
    simp only [pairMeanB]
    push_cast
    rfl
  rw [he, pairMeanFourier_add _ _ hs (hs.comp_sub_right 1)]
  have hsub := pairMeanFourier_sub (fun t => (pairMeanSinc (t/2):ℂ)^2) 1 ξ
  rw [hsub, pairMeanFourier_div (fun t : ℝ => (pairMeanSinc t:ℂ)^2) 2 ξ (by norm_num), pairMeanSinc_sq_fourier]
  norm_num
  ring

end
end HigherCorrelations
