import HigherCorrelations.ReplacementTupleDecay
import HigherCorrelations.OccurrenceSummability
import HigherCorrelations.TripleBudgetAccounting

/-! UNCONDITIONAL summability at fixed height, before taking any zero cutoff limit. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped ContDiff

theorem replacement_anchor_decay_summable (T a A : ℝ) (ha : 0 < a) (hA : 0 ≤ A)
    (p : ℕ) (hp : 4 < p) (f : ReplacementTriple → ℂ)
    (hz : ∀ v, occurrenceOrdinate (v 0) ∉ Icc T (2*T) → f v=0)
    (hf : ∀ v, ‖f v‖ ≤ A/(1+max |(actualGaps a v).1| |(actualGaps a v).2|)^p) :
    Summable (fun v => ‖f v‖) := by
  classical
  obtain ⟨C,hC,hcount⟩ := actual_shell_count T a ha
  have hd (t : AnchoredTriple T) : ‖f (anchoredToTriple t)‖ ≤ A/(1+anchoredRadius T a t)^p :=
    hf (anchoredToTriple t)
  have hs : Summable (fun t : AnchoredTriple T => ‖f (anchoredToTriple t)‖) :=
    dyadic_summable_norm (actualOccurrenceShells T a ha)
      (fun t => f (anchoredToTriple t)) A C hA hC 4 p hp hcount
      (radius_decay_to_shell (actualOccurrenceShells T a ha) (fun t => f (anchoredToTriple t))
        (anchoredRadius T a) A hA p (actual_shell_radius_lower T a ha) hd)
  let e : AnchoredTriple T ≃ {v : ReplacementTriple // T ≤ occurrenceOrdinate (v 0) ∧ occurrenceOrdinate (v 0) ≤ 2*T} :=
    { toFun t := ⟨anchoredToTriple t,t.1.property⟩
      invFun t := (⟨t.val 0,t.property⟩,t.val 1,t.val 2)
      left_inv _ := rfl
      right_inv t := by apply Subtype.ext; funext j; fin_cases j <;> rfl }
  have ht : Summable (fun t : {v : ReplacementTriple // T ≤ occurrenceOrdinate (v 0) ∧ occurrenceOrdinate (v 0) ≤ 2*T} => ‖f t.val‖) :=
    by
      apply (Equiv.summable_iff e (f := fun t => ‖f t.val‖)).mp
      dsimp only [Function.comp_def, e, Equiv.coe_fn_mk]
      exact hs
  have hi : Summable ({v : ReplacementTriple | T ≤ occurrenceOrdinate (v 0) ∧
      occurrenceOrdinate (v 0) ≤ 2*T}.indicator (fun v => ‖f v‖)) :=
    summable_subtype_iff_indicator.mp ht
  apply hi.congr
  intro v
  by_cases hm : T ≤ occurrenceOrdinate (v 0) ∧ occurrenceOrdinate (v 0) ≤ 2*T
  · simp [hm]
  · simp [hm, hz v hm]

theorem replacementWeight_bounds (w : ℝ → ℝ) (hw : TripleBudgetWeight w) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ u, |w u| ≤ W := by
  have hc : HasCompactSupport w := HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc (tripleBudgetWeight_support w hw)
  obtain ⟨W,hW⟩ := hc.exists_bound_of_continuous hw.smooth.continuous
  refine ⟨max W 0, le_max_right _ _,fun u => ?_⟩
  have hh : |w u| ≤ W := by simpa [Real.norm_eq_abs] using hW u
  exact hh.trans (le_max_left _ _)

theorem replacementWeight_zero (w : ℝ → ℝ) (hw : TripleBudgetWeight w) (T : ℝ)
    (hT : 0 < T) (v : ReplacementTriple) (hv : occurrenceOrdinate (v 0) ∉ Icc T (2*T)) :
    w (occurrenceOrdinate (v 0)/T)=0 := by
  by_contra hn
  have h := tripleBudgetWeight_support w hw hn
  apply hv
  exact ⟨(le_div_iff₀ hT).mp h.1 |>.trans' (by simp),
    (div_le_iff₀ hT).mp h.2⟩

theorem replacementMomentTerm_nonneg (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (T s : ℝ) (hq : 0 ≤ Real.log T) (v : ReplacementTriple) :
    0 ≤ replacementMomentTerm w T s v := by
  have hx := (replacementHorizontal_bounds T hq v).1
  have hr := replacementRadius_nonneg T v
  unfold replacementMomentTerm
  have hw := hw.nonneg (occurrenceOrdinate (v 0)/T)
  positivity

theorem replacementMoment_summable (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (T s : ℝ) (hT : 2*Real.pi*Real.exp 1 ≤ T) (hs : 0 < s) :
    Summable (replacementMomentTerm w T s) := by
  have ht := replacementHeight_bounds T hT
  obtain ⟨W,hW,hwb⟩ := replacementWeight_bounds w hw
  let A := W*(Real.log T/2)^2*(1+Real.log T/2)^24*Real.exp (2*s*(Real.log T/2))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb (v) : ‖(replacementMomentTerm w T s v:ℂ)‖ ≤ A/(1+replacementRadius T v)^20 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (replacementMomentTerm_nonneg w hw T s ht.2.1.le v)]
    unfold replacementMomentTerm
    dsimp [A]
    have hx := replacementHorizontal_bounds T ht.2.1.le v
    have hx0 := hx.1
    have hwbnd := (le_abs_self _).trans (hwb (occurrenceOrdinate (v 0)/T))
    gcongr <;> first | exact hw.nonneg _ | exact hx.2.1 | positivity
  have hsum := replacement_anchor_decay_summable T (meanSpacing T) A ht.2.2.1 hA 20 (by norm_num)
    (fun v => (replacementMomentTerm w T s v:ℂ))
    (fun v hv => by simp [replacementMomentTerm, replacementWeight_zero w hw T ht.1 v hv]) hb
  have he (v) : ‖(replacementMomentTerm w T s v:ℂ)‖=replacementMomentTerm w T s v := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (replacementMomentTerm_nonneg w hw T s ht.2.1.le v)]
  simpa only [he] using hsum

theorem replacementTuple_weighted_summable (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Summable (fun v => ‖(w (occurrenceOrdinate (v 0)/T):ℂ)*replacementTuple φ T v‖) := by
  have ht := replacementHeight_bounds T hT
  obtain ⟨W,hW,hwb⟩ := replacementWeight_bounds w hw
  let A := W*replacementDecayConstant*replacementP24 φ*(Real.log T/2)^2*
    (1+Real.log T/2)^22*Real.exp (2*s*(Real.log T/2))
  have hP := replacementP24_nonneg φ
  have hC : 0 ≤ replacementDecayConstant := by unfold replacementDecayConstant; positivity
  apply replacement_anchor_decay_summable T (meanSpacing T) A ht.2.2.1
    (by dsimp [A]; positivity) 22 (by norm_num)
  · intro v hv
    simp [replacementWeight_zero w hw T ht.1 v hv]
  · intro v
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hx := replacementHorizontal_bounds T ht.2.1.le v
    have hx0 := hx.1
    have hb := replacementTuple_bound φ hφ hc s T hs hs1 hT hsupp v
    calc
      _ ≤ W*(replacementDecayConstant*replacementP24 φ*(replacementHorizontal T v)^2*
        (1+replacementHorizontal T v)^22*Real.exp (2*s*replacementHorizontal T v)/(1+replacementRadius T v)^22) :=
        mul_le_mul (hwb _) hb (norm_nonneg _) hW
      _ ≤ A/(1+replacementRadius T v)^22 := by
        rw [← mul_div_assoc]
        dsimp [A]
        simp only [← mul_assoc]
        gcongr <;> first | exact hx.2.1 | positivity

end
end HigherCorrelations
