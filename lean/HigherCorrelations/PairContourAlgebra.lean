import HigherCorrelations.PairExactDefinitions
import HigherCorrelations.PairedMellinBounds

/-! Algebraic identifications used in the contour proof. UNCONDITIONAL.
Signs are exposed before applying the residue theorem. -/
namespace HigherCorrelations
noncomputable section

theorem pairSpectralPoint_re (t : ℝ) : (pairSpectralPoint t).re = 1/2 := by
  simp [pairSpectralPoint]

theorem pairSpectralPoint_im (t : ℝ) : (pairSpectralPoint t).im = t := by
  simp [pairSpectralPoint]

theorem pairContourKernel_denominator_factor (t : ℝ) (z : ℂ) :
    (z-pairSpectralPoint t)^2-1 =
      (z-(pairSpectralPoint t+1))*(z-(pairSpectralPoint t-1)) := by ring

theorem pairContourKernel_continuousAt (X t : ℝ) (z : ℂ)
    (hzp : z ≠ pairSpectralPoint t + 1) (hzm : z ≠ pairSpectralPoint t - 1) :
    ContinuousAt (pairContourKernel X t) z := by
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · rw [pairContourKernel_denominator_factor]
    exact mul_ne_zero (sub_ne_zero.mpr hzp) (sub_ne_zero.mpr hzm)

theorem pairContourKernel_zero (X t : ℝ) (i : ZeroOccurrence) :
    pairContourKernel X t (occurrenceValue i) = -pairZeroTerm i (X,t) := by
  have hz : occurrenceValue i - pairSpectralPoint t =
      (occurrenceDisplacement i : ℂ) + Complex.I * (occurrenceOrdinate i - t) := by
    apply Complex.ext <;>
      simp [occurrenceDisplacement, occurrenceOrdinate, pairSpectralPoint, Complex.mul_re,
        Complex.mul_im]
  have hd : (occurrenceValue i - pairSpectralPoint t)^2-1 =
      -(1+((t-occurrenceOrdinate i:ℝ)+Complex.I*occurrenceDisplacement i)^2) := by
    rw [hz]
    push_cast
    linear_combination ((occurrenceDisplacement i:ℂ)^2) * Complex.I_sq +
      (((t:ℂ)-(occurrenceOrdinate i:ℂ))^2) * Complex.I_sq
  unfold pairContourKernel pairZeroTerm
  rw [hd, hz, div_neg]

theorem pairContourKernel_pole (X t : ℝ) :
    pairContourKernel X t 1 = -pairPoleCorrection (X,t) := by
  unfold pairContourKernel pairPoleCorrection
  have hd : (1-pairSpectralPoint t)^2-1 =
      -(pairSpectralPoint t*(2-pairSpectralPoint t)) := by ring
  rw [hd, div_neg]

theorem pairContourKernel_trivial (X t : ℝ) (n : ℕ) :
    pairContourKernel X t (-2*(n+1 : ℂ)) = pairTrivialTerm n (X,t) := by
  unfold pairContourKernel pairTrivialTerm
  congr 1
  ring

theorem pairContourKernel_right (X t v : ℝ) :
    pairContourKernel X t (5/2 + (v:ℂ)*Complex.I) =
      pairedMellinIntegrand X (v-t) := by
  have hz : (5/2 : ℂ)+(v:ℂ)*Complex.I-pairSpectralPoint t =
      2+((v-t:ℝ):ℂ)*Complex.I := by unfold pairSpectralPoint; push_cast; ring
  simp only [pairContourKernel, pairedMellinIntegrand, hz, mul_comm (Real.log X : ℂ)]

theorem pairContourKernel_right_bound (X t v : ℝ) (hX : 0 < X) :
    ‖pairContourKernel X t (5/2 + (v:ℂ)*Complex.I)‖ ≤
      2*X^2/(1+(v-t)^2) := by
  rw [pairContourKernel_right]
  exact pairedMellinIntegrand_bound X (v-t) hX

end
end HigherCorrelations
