import HigherCorrelations.PairMeanKernelTransforms

/-! UNCONDITIONAL kernel masses and exact support endpoints. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex

theorem pairMeanTriangle_convolution_zero (ξ : ℝ) (hξ : 2 ≤ |ξ|) :
    pairMeanConvolution pairMeanTriangle pairMeanTriangle ξ = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  change pairMeanTriangle u*pairMeanTriangle (ξ-u) = 0
  by_cases hu : 1 ≤ |u|
  · rw [pairMeanTriangle_eq_zero u hu, zero_mul]
  · have hv : 1 ≤ |ξ-u| := by
      have ha := abs_add_le u (ξ-u)
      rw [show u+(ξ-u) = ξ by ring] at ha
      linarith
    rw [pairMeanTriangle_eq_zero (ξ-u) hv, mul_zero]

theorem pairMeanK_fourier_zero (ξ : ℝ) (hξ : 1 ≤ |ξ|) :
    pairMeanFourier (fun t => (pairMeanK t:ℂ)) ξ = 0 := by
  rw [pairMeanK_fourier, pairMeanTriangle_convolution_zero]
  · simp
  · rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith

theorem pairMeanB_fourier_zero (ξ : ℝ) (hξ : 1/2 ≤ |ξ|) :
    pairMeanFourier (fun t => (pairMeanB t:ℂ)) ξ = 0 := by
  rw [pairMeanB_fourier, pairMeanTriangle_eq_zero]
  · simp
  · rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith

theorem pairMeanTriangle_square_mass : (∫ u : ℝ, pairMeanTriangle u^2) = 2/3 := by
  have hs : (∫ u in Set.Icc (-1:ℝ) 1, pairMeanTriangle u^2) =
      ∫ u : ℝ, pairMeanTriangle u^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [pairMeanTriangle_eq_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · exact (by linarith : (1:ℝ) ≤ -u).trans (neg_le_abs u)
    · exact (le_of_lt hu).trans (le_abs_self u)
  rw [← hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  have hi : IntervalIntegrable (fun u : ℝ => pairMeanTriangle u^2) volume (-1) 0 :=
    (pairMeanTriangle_continuous.pow 2).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun u : ℝ => pairMeanTriangle u^2) volume 0 1 :=
    (pairMeanTriangle_continuous.pow 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi hj]
  have hl : (∫ u : ℝ in (-1)..0, pairMeanTriangle u^2) = ∫ u : ℝ in (-1)..0, (1+u)^2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0),Set.mem_Icc] at hu
    change pairMeanTriangle u^2 = (1+u)^2
    simp only [pairMeanTriangle]
    rw [abs_of_nonpos hu.2,max_eq_right (by linarith : 0 ≤ 1- -u)]
    ring
  have hr : (∫ u : ℝ in 0..1, pairMeanTriangle u^2) = ∫ u : ℝ in 0..1, (1-u)^2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),Set.mem_Icc] at hu
    change pairMeanTriangle u^2 = (1-u)^2
    simp only [pairMeanTriangle]
    rw [abs_of_nonneg hu.1,max_eq_right (by linarith : 0 ≤ 1-u)]
  rw [hl,hr]
  have il : (∫ u : ℝ in (-1)..0, (1+u)^2) = 1/3 := by
    have hder (u : ℝ) : HasDerivAt (fun u : ℝ => (1+u)^3/3) ((1+u)^2) u := by
      convert (((hasDerivAt_id u).const_add 1).pow 3).div_const 3 using 1 <;> simp only [id_eq, Pi.pow_apply, Pi.neg_apply] <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hder u)
      ((by fun_prop : Continuous (fun u : ℝ => (1+u)^2)).intervalIntegrable _ _)]
    norm_num
  have ir : (∫ u : ℝ in 0..1, (1-u)^2) = 1/3 := by
    have hder (u : ℝ) : HasDerivAt (fun u : ℝ => -(1-u)^3/3) ((1-u)^2) u := by
      convert ((((hasDerivAt_id u).const_sub 1).pow 3).neg).div_const 3 using 1 <;> simp only [id_eq, Pi.pow_apply, Pi.neg_apply] <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hder u)
      ((by fun_prop : Continuous (fun u : ℝ => (1-u)^2)).intervalIntegrable _ _)]
    norm_num
  rw [il,ir]
  norm_num

theorem pairMeanK_mass : (∫ u : ℝ, pairMeanK u) = 1 := by
  have h := pairMeanK_fourier 0
  rw [pairMeanFourier_zero, integral_complex_ofReal] at h
  have ht : pairMeanConvolution pairMeanTriangle pairMeanTriangle 0 = 2/3 := by
    unfold pairMeanConvolution
    simpa only [zero_sub, pairMeanTriangle, abs_neg, ← pow_two] using pairMeanTriangle_square_mass
  norm_num [ht] at h
  exact_mod_cast h

theorem pairMeanB_mass : (∫ u : ℝ, pairMeanB u) = 4 := by
  have h := pairMeanB_fourier 0
  rw [pairMeanFourier_zero, integral_complex_ofReal] at h
  norm_num [pairMeanCharacter,pairMeanTriangle] at h
  exact_mod_cast h

end
end HigherCorrelations
