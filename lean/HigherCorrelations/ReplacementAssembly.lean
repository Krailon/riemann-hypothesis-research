import HigherCorrelations.ReplacementSummedBounds

/-! UNCONDITIONAL endpoint and cutoff interfaces for constant-kernel replacement.
No density-based vanishing or kernel-free signed-error limit is asserted. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

theorem replacementTuple_zero_test (T : ℝ) (v : ReplacementTriple) :
    replacementTuple (fun _ => 0) T v=0 := by
  simp [replacementTuple, complexFourier]

theorem replacementTuple_zero_displacement (φ : ℝ × ℝ → ℂ) (T : ℝ) (v : ReplacementTriple)
    (hv : ∀ j, occurrenceDisplacement (v j)=0) : replacementTuple φ T v=0 := by
  simp [replacementTuple, replacementCosh, replacementDelta, hv, complexFourier]

theorem replacementError_zero_test (w : ℝ → ℝ) (T : ℝ) :
    replacementError w (fun _ => 0) T=0 := by
  simp [replacementError, replacementTerm, replacementTuple_zero_test]

theorem replacementMoment_nonneg (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (T s : ℝ) (hT : 2*Real.pi*Real.exp 1 ≤ T) : 0 ≤ replacementMoment w T s := by
  have ht := replacementHeight_bounds T hT
  exact div_nonneg (tsum_nonneg (replacementMomentTerm_nonneg w hw T s ht.2.1.le))
    (mul_nonneg ht.1.le ht.2.1.le)

theorem replacementKernel_equal_ordinates (T : ℝ) (hT : uniformHeightThreshold ≤ T)
    (v : ReplacementTriple) (h1 : occurrenceOrdinate (v 1)=occurrenceOrdinate (v 0))
    (h2 : occurrenceOrdinate (v 2)=occurrenceOrdinate (v 0)) :
    ‖replacementKernel v-kernelBenchmark‖ ≤ replacementScaleConstant*
      (replacementHorizontal T v)^2/(Real.log T)^2 := by
  simpa [replacementRadius, actualGaps, h1, h2] using replacementKernel_scaled T hT v

theorem replacementKernel_height_endpoint (v : ReplacementTriple) :
    ‖replacementKernel v-kernelBenchmark‖ ≤ replacementScaleConstant*
      ((replacementRadius uniformHeightThreshold v)^2+(replacementHorizontal uniformHeightThreshold v)^2)/
        (Real.log uniformHeightThreshold)^2 :=
  replacementKernel_scaled _ le_rfl v

theorem replacementTuple_height_endpoint (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (v : ReplacementTriple) :
    ‖replacementTuple φ (2*Real.pi*Real.exp 1) v‖ ≤ replacementDecayConstant*replacementP24 φ*
      (replacementHorizontal (2*Real.pi*Real.exp 1) v)^2*(1+replacementHorizontal (2*Real.pi*Real.exp 1) v)^22*
      Real.exp (2*s*replacementHorizontal (2*Real.pi*Real.exp 1) v)/
        (1+replacementRadius (2*Real.pi*Real.exp 1) v)^22 :=
  replacementTuple_bound φ hφ hc s _ hs hs1 le_rfl hsupp v

theorem replacementError_normalization (T : ℝ) :
    (16/(3*T*Real.log T):ℂ)*kernelBenchmark = (2*Real.pi/(T*Real.log T):ℂ) := by
  unfold kernelBenchmark
  ring

theorem replacementConstantError_cutoff (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => (16/(3*T*Real.log T):ℂ)*
      ∑ v ∈ tripleDomain S, (w (occurrenceOrdinate (v 0)/T):ℂ)*kernelBenchmark*replacementTuple φ T v)
      atTop (𝓝 (replacementConstantError w φ T)) :=
  (triple_cutoff_limit _ (replacement_errors_summable w hw φ hφ hc s T hs hs1 hT hsupp).2.1).const_mul _

theorem replacementEvenError_cutoff (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => (16/(3*T*Real.log T):ℂ)*
      ∑ v ∈ tripleDomain S, (w (occurrenceOrdinate (v 0)/T):ℂ)*replacementKernel v*replacementTuple φ T v)
      atTop (𝓝 (replacementEvenError w φ T)) :=
  (triple_cutoff_limit _ (replacement_errors_summable w hw φ hφ hc s T hs hs1 hT hsupp).2.2).const_mul _

end
end HigherCorrelations
