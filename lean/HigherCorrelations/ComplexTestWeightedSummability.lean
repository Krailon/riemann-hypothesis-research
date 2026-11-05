import HigherCorrelations.SignedCoefficientBound
import HigherCorrelations.TripleTestDefinitions

/-! UNCONDITIONAL complex-test bounds on the full signed support margin.
The imaginary parts of the arguments are retained. No smoothing normalization
or positivity assumption is used by the weighted-series interface. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem signedTest_integrand_bound (φ : ℝ × ℝ → ℂ) (κ T : ℝ)
    (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ)
    (v : MasterTriple) (p : ℝ × ℝ) :
    ‖φ p*Complex.exp (2*Real.pi*Complex.I*
      ((tripleTestArguments T v).1*p.1+(tripleTestArguments T v).2*p.2))‖ ≤
        ‖φ p‖*(tripleTestBase T)^(1-κ) := by
  by_cases hz : φ p=0
  · simp [hz]
  have hp := hs (subset_tsupport φ hz)
  have hB := (tripleTestBase_bounds T hT).2.1
  rw [← tripleTest_phase T hT p v,norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((signed_coefficient_bound _ hB p (tripleTestToMaster v)).trans
      (Real.rpow_le_rpow_of_exponent_le hB.le hp)) (norm_nonneg _)

theorem signedTest_integrable (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ)
    (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) (v : MasterTriple) :
    Integrable (fun p : ℝ × ℝ => φ p*Complex.exp (2*Real.pi*Complex.I*
      ((tripleTestArguments T v).1*p.1+(tripleTestArguments T v).2*p.2))) := by
  apply (hφ.norm.mul_const ((tripleTestBase T)^(1-κ))).mono'
    (hφ.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop)))
  exact Filter.Eventually.of_forall (signedTest_integrand_bound φ κ T hT hs v)

theorem signedTest_bound (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ)
    (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) (v : MasterTriple) :
    ‖complexFourier φ (tripleTestArguments T v)‖ ≤ tripleTestL1 φ*(tripleTestBase T)^(1-κ) := by
  apply (norm_integral_le_integral_norm _).trans
  have h := integral_mono (signedTest_integrable φ hφ κ T hT hs v).norm
    (hφ.norm.mul_const _) (signedTest_integrand_bound φ κ T hT hs v)
  simpa only [integral_mul_const,tripleTestL1] using h

theorem signedTest_weighted_summable_bound (f : MasterTriple → ℂ)
    (hf : Summable (fun v => ‖f v‖)) (D : ℝ) (hD : (∑' v, ‖f v‖)≤D)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ)
    (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) :
    Summable (fun v => ‖f v*complexFourier φ (tripleTestArguments T v)‖) ∧
    (∑' v, ‖f v*complexFourier φ (tripleTestArguments T v)‖) ≤
      tripleTestL1 φ*(tripleTestBase T)^(1-κ)*D := by
  have hC : 0≤tripleTestL1 φ*(tripleTestBase T)^(1-κ) := by
    have hB := (tripleTestBase_bounds T hT).2.1
    unfold tripleTestL1
    positivity
  have hp (v : MasterTriple) : ‖f v*complexFourier φ (tripleTestArguments T v)‖ ≤
      ‖f v‖*(tripleTestL1 φ*(tripleTestBase T)^(1-κ)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (signedTest_bound φ hφ κ T hT hs v) (norm_nonneg _)
  have hb := hf.mul_right (tripleTestL1 φ*(tripleTestBase T)^(1-κ))
  have hw := hb.of_nonneg_of_le (fun _ => norm_nonneg _) hp
  refine ⟨hw,?_⟩
  have h := hw.tsum_le_tsum hp hb
  rw [tsum_mul_right] at h
  exact h.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hD hC)

end
end HigherCorrelations
