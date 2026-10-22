import HigherCorrelations.PairFourierIdentity

/-! UNCONDITIONAL exact change from log T to local mean-spacing units.
The Jacobian is independent of the change of normalization. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairScale_positive (T : ℝ) (hT : 2*Real.pi<T) :
    0 < meanSpacing T ∧ 0<pairSourceSpacing T ∧ 0<pairScaleRatio T := by
  have hp := Real.pi_pos
  have hT1 : 1<T := by linarith [Real.pi_gt_three]
  have hl : 0<Real.log (T/(2*Real.pi)) := Real.log_pos ((one_lt_div (by positivity)).mpr hT)
  have hA : 0<pairSourceSpacing T := div_pos (Real.log_pos hT1) (by positivity)
  have hL : 0 < meanSpacing T := div_pos hl (by positivity)
  exact ⟨hL,hA,div_pos hA hL⟩

theorem pairScale_normalization (T : ℝ) (hT : 2*Real.pi<T) :
    pairNormalization T = pairScaleRatio T*T*meanSpacing T := by
  have hL := ne_of_gt (pairScale_positive T hT).1
  unfold pairScaleRatio pairNormalization pairSourceSpacing
  field_simp

theorem pairScale_argument (T : ℝ) (hT : 2*Real.pi<T) (i j : ZeroOccurrence) :
    Complex.I*pairSourceSpacing T*(occurrenceValue i-occurrenceValue j) =
      (pairScaleRatio T*(meanSpacing T*(occurrenceOrdinate j-occurrenceOrdinate i)) : ℝ) +
        Complex.I*((pairHorizontalCoordinate T i-pairHorizontalCoordinate T j)/(2*Real.pi) : ℝ) := by
  have hL := ne_of_gt (pairScale_positive T hT).1
  have hq : pairScaleRatio T*meanSpacing T = pairSourceSpacing T := div_mul_cancel₀ _ hL
  rw [← mul_assoc, hq]
  have he (A : ℝ) (z w : ℂ) : Complex.I*(A:ℂ)*(z-w) =
      (A*(w.im-z.im) : ℝ)+Complex.I*(A*(z.re-w.re) : ℝ) := by
    apply Complex.ext <;> simp; ring
  rw [he]
  congr 2
  unfold pairHorizontalCoordinate occurrenceDisplacement pairSourceSpacing
  push_cast
  ring

theorem pairScale_phase (T a : ℝ) (hT : 2*Real.pi<T) (i j : ZeroOccurrence) :
    Complex.exp (Complex.I*(a*(occurrenceOrdinate i-occurrenceOrdinate j)*Real.log T : ℝ)) =
      Complex.exp (-2*Real.pi*Complex.I*(pairScaleRatio T*a : ℝ)*
        (meanSpacing T*(occurrenceOrdinate j-occurrenceOrdinate i) : ℝ)) := by
  have hL := ne_of_gt (pairScale_positive T hT).1
  have hq : pairScaleRatio T*meanSpacing T = pairSourceSpacing T := div_mul_cancel₀ _ hL
  congr 1
  have he : -2*Real.pi*(pairScaleRatio T*a)*(meanSpacing T*(occurrenceOrdinate j-occurrenceOrdinate i)) =
      a*(occurrenceOrdinate i-occurrenceOrdinate j)*Real.log T := by
    calc
      _ = -2*Real.pi*(pairScaleRatio T*meanSpacing T)*a*(occurrenceOrdinate j-occurrenceOrdinate i) := by ring
      _ = _ := by rw [hq]; unfold pairSourceSpacing; field_simp; ring
  have hh := congrArg (fun r : ℝ => Complex.I*(r:ℂ)) he
  push_cast at hh
  convert hh.symm using 1 <;> push_cast <;> ring

theorem pairScale_support (T a : ℝ) (hT : 2*Real.pi<T) :
    |a|≤1 ↔ |pairScaleRatio T*a|≤pairScaleRatio T := by
  have hq := (pairScale_positive T hT).2.2
  rw [abs_mul,abs_of_pos hq]
  simpa only [one_mul,mul_one,mul_comm] using (mul_le_mul_iff_left₀ hq (b := |a|) (c := 1)).symm

theorem pairScale_power (T ξ : ℝ) (hT : 2*Real.pi<T) :
    (T/(2*Real.pi))^ξ = T^(ξ/pairScaleRatio T) := by
  have ht : 0<T := lt_trans (by positivity) hT
  have hp : 0<T/(2*Real.pi) := div_pos ht (by positivity)
  have hl := ne_of_gt (Real.log_pos (show 1<T by linarith [Real.pi_gt_three]))
  have hll : Real.log (T/(2*Real.pi)) ≠ 0 := ne_of_gt
    (Real.log_pos ((one_lt_div (by positivity)).mpr hT))
  rw [Real.rpow_def_of_pos hp,Real.rpow_def_of_pos ht]
  congr 1
  unfold pairScaleRatio pairSourceSpacing meanSpacing
  field_simp

theorem pairScale_correlation (T ξ : ℝ) (hT : 2*Real.pi<T) :
    pairLocalCorrelation T ξ = pairScaleRatio T*pairNormalizedCorrelation T (ξ/pairScaleRatio T) := by
  have ht : T ≠ 0 := ne_of_gt (lt_trans (by positivity) hT)
  have hl := ne_of_gt (Real.log_pos (show 1<T by linarith [Real.pi_gt_three]))
  have hL := ne_of_gt (pairScale_positive T hT).1
  unfold pairLocalCorrelation pairNormalizedCorrelation
  rw [pairScale_power T ξ hT]
  unfold pairScaleRatio pairSourceSpacing
  field_simp

theorem pairScale_jacobian (T : ℝ) (hT : 2*Real.pi<T) (f : ℝ → ℂ) :
    (∫ ξ : ℝ, f (ξ/pairScaleRatio T)) =
      (pairScaleRatio T : ℂ)*(∫ a : ℝ, f a) := by
  simpa only [abs_of_pos (pairScale_positive T hT).2.2,Complex.real_smul] using
    Measure.integral_comp_div f (pairScaleRatio T)

theorem pairScale_integrated (T : ℝ) (hT : 2*Real.pi<T) (g : ℝ → ℂ) :
    (∫ ξ : ℝ, g (ξ/pairScaleRatio T)*(pairLocalCorrelation T ξ : ℂ)) =
      (pairScaleRatio T : ℂ)^2*(∫ a : ℝ, g a*(pairNormalizedCorrelation T a : ℂ)) := by
  simp_rw [pairScale_correlation T _ hT,Complex.ofReal_mul,
    show ∀ ξ : ℝ, g (ξ/pairScaleRatio T)*((pairScaleRatio T : ℂ)*
      (pairNormalizedCorrelation T (ξ/pairScaleRatio T) : ℂ)) =
      (pairScaleRatio T : ℂ)*(g (ξ/pairScaleRatio T)*
        (pairNormalizedCorrelation T (ξ/pairScaleRatio T) : ℂ)) from fun ξ => by ring]
  rw [integral_const_mul,pairScale_jacobian T hT (fun a => g a*(pairNormalizedCorrelation T a : ℂ))]
  ring

end
end HigherCorrelations
