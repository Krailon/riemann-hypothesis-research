import HigherCorrelations.PairEulerSeries
import HigherCorrelations.PairContourAlgebra
import HigherCorrelations.PairedMellin
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolutely convergent prime expansion of the right contour. UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem pairEuler_mul_kernel (n : ℕ) (X t : ℝ) (z : ℂ) (hX : 0 < X) :
    pairEulerTerm n z * pairContourKernel X t z =
      pairEulerTerm n (pairSpectralPoint t) * pairContourKernel (X/(n+1)) t z := by
  have hn : (n+1:ℝ) ≠ 0 := by positivity
  unfold pairEulerTerm pairContourKernel
  rw [Real.log_div hX.ne' hn]
  push_cast
  simp only [← mul_div_assoc]
  congr 1
  calc
    _ = (ArithmeticFunction.vonMangoldt (n+1):ℂ) * 2 *
      (Complex.exp ((Real.log (n+1:ℝ):ℂ)*(-z)) *
        Complex.exp ((Real.log X:ℂ)*(z-pairSpectralPoint t))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      have he : (Real.log (n+1:ℝ):ℂ)*(-z) + (Real.log X:ℂ)*(z-pairSpectralPoint t) =
          (Real.log (n+1:ℝ):ℂ)*(-pairSpectralPoint t) +
            ((Real.log X:ℂ)-(Real.log (n+1:ℝ):ℂ))*(z-pairSpectralPoint t) := by ring
      rw [he, Complex.exp_add]
      ring

theorem pairEulerContour_integrable (n : ℕ) (X t : ℝ) (hX : 0 < X) :
    Integrable (fun v : ℝ => pairEulerTerm n (5/2+(v:ℂ)*Complex.I) *
      pairContourKernel X t (5/2+(v:ℂ)*Complex.I)) := by
  simp_rw [pairEuler_mul_kernel n X t _ hX, pairContourKernel_right]
  exact ((pairedMellinIntegrand_integrable (X/(n+1)) (by positivity)).comp_sub_right t).const_mul _

theorem pairEulerContour_bound (n : ℕ) (X t v : ℝ) (hX : 0 < X) :
    ‖pairEulerTerm n (5/2+(v:ℂ)*Complex.I) *
      pairContourKernel X t (5/2+(v:ℂ)*Complex.I)‖ ≤
      ‖pairEulerTerm n (5/2)‖ * (2*X^2/(1+(v-t)^2)) := by
  rw [norm_mul]
  have he := pairEulerTerm_norm_vertical n (5/2) v
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
  rw [he]
  exact mul_le_mul_of_nonneg_left (pairContourKernel_right_bound X t v hX) (norm_nonneg _)

theorem pairEulerContour_hasSum (X t v : ℝ) :
    HasSum (fun n => pairEulerTerm n (5/2+(v:ℂ)*Complex.I) *
      pairContourKernel X t (5/2+(v:ℂ)*Complex.I))
      (pairContourIntegrand X t (5/2+(v:ℂ)*Complex.I)) := by
  have hz : 1 < ((5/2:ℂ)+(v:ℂ)*Complex.I).re := by norm_num
  have h := (pairEulerTerm_summable _ hz).hasSum.mul_right
    (pairContourKernel X t (5/2+(v:ℂ)*Complex.I))
  rwa [pairEulerSeries _ hz] at h

theorem pairEulerContour_integral_hasSum (X t : ℝ) (hX : 0 < X) :
    HasSum (fun n => ∫ v : ℝ, pairEulerTerm n (5/2+(v:ℂ)*Complex.I) *
      pairContourKernel X t (5/2+(v:ℂ)*Complex.I))
      (∫ v : ℝ, pairContourIntegrand X t (5/2+(v:ℂ)*Complex.I)) := by
  have hs : Summable (fun n => ‖pairEulerTerm n (5/2)‖) :=
    (pairEulerTerm_summable (5/2) (by norm_num)).norm
  apply hasSum_integral_of_dominated_convergence
    (fun n v => ‖pairEulerTerm n (5/2)‖ * (2*X^2/(1+(v-t)^2)))
  · exact fun n => (pairEulerContour_integrable n X t hX).aestronglyMeasurable
  · intro n
    filter_upwards [] with v using pairEulerContour_bound n X t v hX
  · filter_upwards [] with v using hs.mul_right _
  · simp_rw [tsum_mul_right]
    have h := ((integrable_inv_one_add_sq.comp_sub_right t).const_mul (2*X^2)).const_mul
      (∑' n, ‖pairEulerTerm n (5/2)‖)
    simpa [div_eq_mul_inv] using h
  · filter_upwards [] with v using pairEulerContour_hasSum X t v

theorem pairEulerContour_integral (n : ℕ) (X t : ℝ) (hX : 0 < X) :
    (1/(2*(Real.pi:ℂ))) * (∫ v : ℝ, pairEulerTerm n (5/2+(v:ℂ)*Complex.I) *
      pairContourKernel X t (5/2+(v:ℂ)*Complex.I)) =
      pairEulerTerm n (pairSpectralPoint t) * pairedMellinKernel (X/(n+1)) := by
  simp_rw [pairEuler_mul_kernel n X t _ hX, pairContourKernel_right]
  rw [integral_const_mul, integral_sub_right_eq_self]
  simp only [pairedMellinKernel, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem pairRightIntegral_hasSum (X t : ℝ) (hX : 0 < X) :
    HasSum (fun n => pairEulerTerm n (pairSpectralPoint t) * pairedMellinKernel (X/(n+1)))
      (pairRightIntegral (X,t)) := by
  have h := (pairEulerContour_integral_hasSum X t hX).mul_left (1/(2*(Real.pi:ℂ)))
  simpa only [pairEulerContour_integral _ X t hX, pairRightIntegral] using h

end
end HigherCorrelations
