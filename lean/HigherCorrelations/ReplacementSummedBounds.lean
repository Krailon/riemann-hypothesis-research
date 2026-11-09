import HigherCorrelations.ReplacementSummability

/-! UNCONDITIONAL absolute convergence, exact splitting and normalized moment bound. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

theorem replacementKernel_global (v : ReplacementTriple) : ‖replacementKernel v‖ ≤ 7*Real.pi/9 :=
  constantKernelEmpty_global_bound _ _ _ (fun j => (occurrence_displacement_lt (v j)).le)

private theorem bounded_kernel_sum (f k : ReplacementTriple → ℂ) (C : ℝ)
    (hf : Summable (fun v => ‖f v‖)) (hk : ∀ v, ‖k v‖ ≤ C) :
    Summable (fun v => ‖k v*f v‖) := by
  apply (hf.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro v
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hk v) (norm_nonneg _)

theorem replacement_errors_summable (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Summable (fun v => ‖replacementTerm w φ T v‖) ∧
    Summable (fun v => ‖(w (occurrenceOrdinate (v 0)/T):ℂ)*kernelBenchmark*replacementTuple φ T v‖) ∧
    Summable (fun v => ‖(w (occurrenceOrdinate (v 0)/T):ℂ)*replacementKernel v*replacementTuple φ T v‖) := by
  let f := fun v => (w (occurrenceOrdinate (v 0)/T):ℂ)*replacementTuple φ T v
  have hf := replacementTuple_weighted_summable w hw φ hφ hc s T hs hs1 hT hsupp
  have hconst := bounded_kernel_sum f (fun _ => kernelBenchmark) ‖kernelBenchmark‖ hf (fun _ => le_rfl)
  have heven := bounded_kernel_sum f replacementKernel (7*Real.pi/9) hf replacementKernel_global
  have hrepl := bounded_kernel_sum f (fun v => replacementKernel v-kernelBenchmark)
    (7*Real.pi/9+‖kernelBenchmark‖) hf (fun v =>
      (norm_sub_le _ _).trans (add_le_add (replacementKernel_global v) le_rfl))
  constructor
  · convert hrepl using 1
    funext v
    congr 1
    dsimp [replacementTerm,f]
    ring
  constructor
  · convert hconst using 1; funext v; congr 1; dsimp [f]; ring
  · convert heven using 1; funext v; congr 1; dsimp [f]; ring

theorem replacement_error_split (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    replacementEvenError w φ T = replacementConstantError w φ T+replacementError w φ T := by
  have hh := replacement_errors_summable w hw φ hφ hc s T hs hs1 hT hsupp
  unfold replacementEvenError replacementConstantError replacementError
  rw [← mul_add, ← hh.2.1.of_norm.tsum_add hh.1.of_norm]
  congr 1
  apply tsum_congr
  intro v
  unfold replacementTerm
  ring

theorem replacement_absorb_decay (r x : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) :
    (r^2+x^2)*(1+x)^22/(1+r)^22 ≤ (1+x)^24/(1+r)^20 := by
  have hr1 : 0 < (1+r) := by linarith
  have hb : r^2+x^2 ≤ (1+r)^2*(1+x)^2 := by
    have h1 : 0 ≤ (1+r)^2-1 := by nlinarith
    have h2 : 0 ≤ (1+x)^2-1 := by nlinarith
    nlinarith [mul_nonneg h1 h2]
  apply (div_le_div_iff₀ (pow_pos hr1 _) (pow_pos hr1 _)).mpr
  have h := mul_le_mul_of_nonneg_right hb (show 0 ≤ (1+x)^22*(1+r)^20 by positivity)
  convert h using 1 <;> ring

theorem replacement_large_height (T : ℝ) (hT : uniformHeightThreshold ≤ T) :
    2*Real.pi*Real.exp 1 ≤ T := by
  apply le_trans _ hT
  unfold uniformHeightThreshold
  gcongr
  linarith [Real.pi_gt_three]

theorem replacementTerm_bound (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : uniformHeightThreshold ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (v : ReplacementTriple) :
    ‖replacementTerm w φ T v‖ ≤
      (replacementScaleConstant*replacementDecayConstant*replacementP24 φ/(Real.log T)^2)*
        replacementMomentTerm w T s v := by
  have ht := replacementHeight_bounds T (replacement_large_height T hT)
  have hx := (replacementHorizontal_bounds T ht.2.1.le v).1
  have hr := replacementRadius_nonneg T v
  have hP := replacementP24_nonneg φ
  have hC : 0 ≤ replacementScaleConstant := by unfold replacementScaleConstant; positivity
  have hD : 0 ≤ replacementDecayConstant := by unfold replacementDecayConstant; positivity
  have hw := hw.nonneg (occurrenceOrdinate (v 0)/T)
  have hk := replacementKernel_scaled T hT v
  have hf := replacementTuple_bound φ hφ hc s T hs hs1 (replacement_large_height T hT) hsupp v
  unfold replacementTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hk hw) hf (norm_nonneg _) (by positivity)).trans
  have ha := mul_le_mul_of_nonneg_left
    (replacement_absorb_decay (replacementRadius T v) (replacementHorizontal T v) hr hx)
    (show 0 ≤ w (occurrenceOrdinate (v 0)/T)*replacementScaleConstant*replacementDecayConstant*
      replacementP24 φ*(replacementHorizontal T v)^2*Real.exp (2*s*replacementHorizontal T v)/(Real.log T)^2 by positivity)
  convert ha using 1 <;> (try unfold replacementMomentTerm) <;> ring

theorem replacementError_bound (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : uniformHeightThreshold ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    ‖replacementError w φ T‖ ≤
      ((16/3:ℝ)*replacementScaleConstant*replacementDecayConstant)*replacementP24 φ/
        (Real.log T)^2*replacementMoment w T s := by
  have hsmall := replacement_large_height T hT
  have ht := replacementHeight_bounds T hsmall
  have htp := ht.1
  have hq := ht.2.1
  have hf := (replacement_errors_summable w hw φ hφ hc s T hs hs1 hsmall hsupp).1
  have hm := replacementMoment_summable w hw T s hsmall hs
  have h := hf.tsum_le_tsum (replacementTerm_bound w hw φ hφ hc s T hs hs1 hT hsupp)
    (hm.mul_left (replacementScaleConstant*replacementDecayConstant*replacementP24 φ/(Real.log T)^2))
  rw [tsum_mul_left] at h
  unfold replacementError
  rw [norm_mul]
  have hn : ‖(16/(3*T*Real.log T):ℂ)‖ = 16/(3*T*Real.log T) := by
    rw [norm_div]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1, abs_of_pos ht.2.1]
    norm_num
  rw [hn]
  have hb := mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hf).trans h)
    (show 0 ≤ 16/(3*T*Real.log T) by positivity)
  convert hb using 1 <;> (try unfold replacementMoment) <;> ring

theorem replacementError_cutoff (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => (16/(3*T*Real.log T):ℂ)*
      ∑ v ∈ tripleDomain S, replacementTerm w φ T v) atTop (𝓝 (replacementError w φ T)) :=
  (triple_cutoff_limit _ (replacement_errors_summable w hw φ hφ hc s T hs hs1 hT hsupp).1).const_mul _

end
end HigherCorrelations
