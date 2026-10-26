import HigherCorrelations.TripleBudgetDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! UNCONDITIONAL decay of the named scalar envelope for fixed positive margin.
This module does not assert a bound for the triple observable. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem tripleBudget_log_height (T : ℝ) (hT : 3≤T) :
    0≤Real.log (2*T+2) ∧ Real.log (2*T+2) ≤ 2*Real.log T := by
  have hT0 : 0<T := by linarith
  constructor
  · exact Real.log_nonneg (by linarith)
  · have h := Real.log_le_log (by linarith : 0<2*T+2) (show 2*T+2≤T^2 by nlinarith)
    rwa [Real.log_pow,Nat.cast_ofNat] at h

theorem tripleBudgetEnvelope_bound (ε Winf W₁ T : ℝ) (hW : 0≤Winf) (hW₁ : 0≤W₁) (hT : 3≤T) :
    0≤tripleBudgetEnvelope ε Winf W₁ T ∧
      tripleBudgetEnvelope ε Winf W₁ T ≤
        (16*(1+Winf+W₁))*(Real.log T^4/T^ε) := by
  have hT0 : 0<T := by linarith
  have hlog := tripleBudget_log_height T hT
  have hp := pow_le_pow_left₀ hlog.1 hlog.2 4
  constructor
  · unfold tripleBudgetEnvelope; positivity
  · have h := mul_le_mul_of_nonneg_left hp (show 0≤(1+Winf+W₁)*T^(-ε) by positivity)
    unfold tripleBudgetEnvelope
    convert h using 1
    rw [Real.rpow_neg hT0.le,mul_pow]
    ring

theorem tripleBudgetEnvelope_tendsto (ε Winf W₁ : ℝ) (hε : 0<ε) (hW : 0≤Winf) (hW₁ : 0≤W₁) :
    Tendsto (tripleBudgetEnvelope ε Winf W₁) atTop (𝓝 0) := by
  have h : Tendsto (fun T : ℝ => Real.log T^4/T^ε) atTop (𝓝 0) := by
    simpa only [show (4:ℝ)=(4:ℕ) by norm_num,Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).tendsto_div_nhds_zero
  have hc := h.const_mul (16*(1+Winf+W₁))
  simp only [mul_zero] at hc
  apply squeeze_zero' _ _ hc
  · exact (eventually_ge_atTop (3:ℝ)).mono (fun T hT => (tripleBudgetEnvelope_bound ε Winf W₁ T hW hW₁ hT).1)
  · exact (eventually_ge_atTop (3:ℝ)).mono (fun T hT => (tripleBudgetEnvelope_bound ε Winf W₁ T hW hW₁ hT).2)

end
end HigherCorrelations
