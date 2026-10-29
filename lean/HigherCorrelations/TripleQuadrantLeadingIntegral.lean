import HigherCorrelations.TripleQuadrantSwap
import HigherCorrelations.TripleBoundaryScales

/-! UNCONDITIONAL integration of the retained main expression, including both axes. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrantOriginLead_integrable (ψ : ℝ × ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (b : ℝ) :
    IntegrableOn (fun p => ψ p*(Real.exp (-(2*b*(p.1+p.2))):ℂ)) tripleQuadrant := by
  apply Integrable.integrableOn
  exact (by fun_prop : Continuous (fun p => ψ p*(Real.exp (-(2*b*(p.1+p.2))):ℂ))).integrable_of_hasCompactSupport hc.mul_right

theorem tripleBoundary_main_frequency (ω : ℝ → ℝ) (T B : ℝ) (hB : 0 < B) (p : ℝ × ℝ) :
    tripleRetainedMain ω T (B^p.1) (B^p.2) =
      Real.log T^3*Real.exp (-(2*Real.log B*(p.1+p.2)))+
      (Real.log T+tripleSmoothingMean ω)*
        (tripleQuadrantAxisKernel (Real.log B) p+tripleQuadrantAxisKernel (Real.log B) p.swap) := by
  rw [tripleRetainedMain,tripleBoundary_G_frequency_exact B hB p,div_eq_mul_one_div,
    tripleBoundary_inverse_product_square B p.1 p.2 hB,← Real.exp_add]
  congr 2
  congr 1
  ring

theorem tripleQuadrant_main_integral (ω : ℝ → ℝ) (T B : ℝ) (hB : 0 < B)
    (ψ : ℝ × ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    (∫ p in tripleQuadrant, ψ p*(tripleRetainedMain ω T (B^p.1) (B^p.2):ℂ)) =
      (Real.log T:ℂ)^3*tripleQuadrantOriginLead ψ (Real.log B)+
      ((Real.log T+tripleSmoothingMean ω:ℝ):ℂ)*
        (tripleQuadrantAxisLead ψ (Real.log B)+
         tripleQuadrantAxisLead (fun p => ψ p.swap) (Real.log B)) := by
  let b := Real.log B
  have hi := (tripleQuadrantOriginLead_integrable ψ hψ hc b).const_mul ((Real.log T:ℂ)^3)
  have hj := tripleQuadrantAxisLead_integrable ψ hψ hc b
  have hk : IntegrableOn (fun p => ψ p*(tripleQuadrantAxisKernel b p.swap:ℂ)) tripleQuadrant := by
    apply Integrable.integrableOn
    exact (hψ.mul (Complex.continuous_ofReal.comp ((tripleQuadrantAxisKernel_continuous b).comp
      (continuous_snd.prodMk continuous_fst)))).integrable_of_hasCompactSupport hc.mul_right
  have he (p : ℝ × ℝ) : ψ p*(tripleRetainedMain ω T (B^p.1) (B^p.2):ℂ) =
      (Real.log T:ℂ)^3*(ψ p*(Real.exp (-(2*b*(p.1+p.2))):ℂ))+
      ((Real.log T+tripleSmoothingMean ω:ℝ):ℂ)*
        (ψ p*(tripleQuadrantAxisKernel b p:ℂ)+ψ p*(tripleQuadrantAxisKernel b p.swap:ℂ)) := by
    rw [tripleBoundary_main_frequency ω T B hB p]
    push_cast
    dsimp [b]
    ring
  simp_rw [he]
  have hjk : IntegrableOn (fun p => ψ p*(tripleQuadrantAxisKernel b p:ℂ)+
      ψ p*(tripleQuadrantAxisKernel b p.swap:ℂ)) tripleQuadrant := hj.add hk
  rw [integral_add hi (hjk.const_mul ((Real.log T+tripleSmoothingMean ω:ℝ):ℂ)),
    integral_const_mul,integral_const_mul,integral_add hj hk]
  have hswap := tripleQuadrant_integral_swap (fun p => ψ p*(tripleQuadrantAxisKernel b p.swap:ℂ))
  have hs : tripleQuadrantAxisLead (fun p => ψ p.swap) b =
      ∫ p in tripleQuadrant, ψ p*(tripleQuadrantAxisKernel b p.swap:ℂ) := by
    simpa only [tripleQuadrantAxisLead,Prod.swap_swap] using hswap
  change _ = _*tripleQuadrantOriginLead ψ b+_*
    (tripleQuadrantAxisLead ψ b+tripleQuadrantAxisLead (fun p => ψ p.swap) b)
  rw [hs]
  rfl 

theorem tripleQuadrantOrigin_scaled_approximation (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (M N b : ℝ) (hN : 0 ≤ N) (hb : 0 < b)
    (hbound : ∀ p ∈ tripleQuadrant, ‖ψ p‖ ≤ M)
    (hD : ∀ p ∈ tripleQuadrant, ‖fderiv ℝ ψ p‖ ≤ N) :
    ‖(b:ℂ)^2*tripleQuadrantOriginLead ψ b-ψ (0,0)/4‖ ≤ N/(4*b) := by
  rw [tripleQuadrantOriginLead,tripleBoundary_origin_substitution ψ b hb]
  have hbC : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  simp only [Complex.ofReal_pow,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero 2 hbC),one_mul]
  exact tripleBoundary_origin_approximation ψ hψ M N b hN hb hbound hD

end
end HigherCorrelations
