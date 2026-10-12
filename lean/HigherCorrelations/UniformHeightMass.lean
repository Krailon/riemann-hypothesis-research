import HigherCorrelations.UniformHeightTails
import HigherCorrelations.IntegralProfile
import HigherCorrelations.RationalKernelBounds

/-! UNCONDITIONAL mass and tail bounds for real-test envelopes and bounded kernel factors. -/
namespace HigherCorrelations
noncomputable section

theorem anchored_decay_mass_uniform (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A : ℝ, uniformHeightThreshold ≤ T →
      1 ≤ a → 0 ≤ A → ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      Summable (fun t => ‖f t‖) ∧ normalizedTripleMass T f ≤ C*A*(Real.log T)^2 := by
  obtain ⟨C,hC,hb⟩ := anchored_decay_tail_uniform p hp
  refine ⟨C,hC,fun T a A hT ha hA f hf => ?_⟩
  have hh := hb T a 0 A hT ha (by norm_num) hA f hf
  let e : AnchoredTriple T ≃ AnchoredTail T a 0 :=
    { toFun := fun t => ⟨t,anchoredRadius_nonneg T a t⟩
      invFun := fun t => t.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : Summable (fun t => ‖f t‖) := e.summable_iff.mpr hh.1
  refine ⟨hs,?_⟩
  have he := e.tsum_eq (fun t => ‖f t.val‖)
  simpa [normalizedTripleMass,← he,e] using hh.2

theorem anchored_decay_strict_tail_uniform (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a R A : ℝ, uniformHeightThreshold ≤ T →
      1 ≤ a → 0 ≤ R → 0 ≤ A → ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      normalizedTripleTail T a R f ≤ C*A*(Real.log T)^2/(1+R)^(p-4) := by
  obtain ⟨C,hC,hb⟩ := anchored_decay_tail_uniform p hp
  refine ⟨C,hC,fun T a R A hT ha hR hA f hf => ?_⟩
  have hh := hb T a R A hT ha hR hA f hf
  let j : {t : AnchoredTriple T // R < anchoredRadius T a t} → AnchoredTail T a R :=
    fun t => ⟨t.val,t.property.le⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (congrArg (fun z : AnchoredTail T a R => z.val) h)
  have hs := (hh.1.comp_injective hj).tsum_le_tsum_of_inj j hj
    (fun t _ => norm_nonneg (f t.val)) (fun _ => le_rfl) hh.1
  exact (div_le_div_of_nonneg_right hs (by obtain ⟨ht,hq,_⟩ := uniformHeightThreshold_bounds hT; positivity)).trans hh.2

theorem bounded_factor_decay {I : Type*} (r : I → ℝ) (f k : I → ℂ) (A B : ℝ)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ)
    (hk : ∀ i, ‖k i‖ ≤ B) (hf : ∀ i, ‖f i‖ ≤ A/(1+r i)^p) :
    ∀ i, ‖k i*f i‖ ≤ (B*A)/(1+r i)^p := by
  intro i
  rw [norm_mul,mul_div_assoc]
  exact mul_le_mul (hk i) (hf i) (norm_nonneg _) hB

theorem weighted_real_test_decay (T a W A : ℝ) (hW : 0 ≤ W) (_hA : 0 ≤ A) (p : ℕ)
    (w : ℝ → ℂ) (F : ℝ × ℝ → ℂ)
    (hw : ∀ x, T ≤ x → x ≤ 2*T → ‖w x‖ ≤ W)
    (hF : ∀ u v : ℝ, ‖F (u,v)‖ ≤ A/(1+max |u| |v|)^p) :
    ∀ t : AnchoredTriple T,
      ‖w (occurrenceOrdinate t.1.val)*F
        (a*(occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val),
         a*(occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val))‖ ≤
        (W*A)/(1+anchoredRadius T a t)^p := by
  intro t
  rw [norm_mul,mul_div_assoc]
  exact mul_le_mul (hw _ t.1.property.1 t.1.property.2) (hF _ _) (norm_nonneg _) hW

theorem project_weighted_mass_tail (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T W A : ℝ, uniformHeightThreshold ≤ T → 0 ≤ W → 0 ≤ A →
      ∀ w : ℝ → ℂ, ∀ F : ℝ × ℝ → ℂ,
      (∀ x, T ≤ x → x ≤ 2*T → ‖w x‖ ≤ W) →
      (∀ u v, ‖F (u,v)‖ ≤ A/(1+max |u| |v|)^p) →
      let f : AnchoredTriple T → ℂ := fun t => w (occurrenceOrdinate t.1.val)*F
        (meanSpacing T*(occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val),
         meanSpacing T*(occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val))
      Summable (fun t => ‖f t‖) ∧ normalizedTripleMass T f ≤ C*W*A*(Real.log T)^2 ∧
      ∀ R : ℝ, 1 ≤ R → normalizedTripleTail T (meanSpacing T) R f ≤
        C*W*A*(Real.log T)^2/R^(p-4) := by
  obtain ⟨C₁,h₁,b₁⟩ := anchored_decay_mass_uniform p hp
  obtain ⟨C₂,h₂,b₂⟩ := anchored_decay_strict_tail_uniform p hp
  refine ⟨C₁+C₂,by positivity,fun T W A hT hW hA w F hw hF => ?_⟩
  dsimp only
  let f : AnchoredTriple T → ℂ := fun t => w (occurrenceOrdinate t.1.val)*F
    (meanSpacing T*(occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val),
     meanSpacing T*(occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val))
  have ha := (uniformHeightThreshold_bounds hT).2.2
  have hf := weighted_real_test_decay T (meanSpacing T) W A hW hA p w F hw hF
  have hm := b₁ T _ (W*A) hT ha (mul_nonneg hW hA) f hf
  refine ⟨hm.1,?_,fun R hR => ?_⟩
  · change normalizedTripleMass T f ≤ _
    have := mul_nonneg h₂.le (mul_nonneg (mul_nonneg hW hA) (sq_nonneg (Real.log T)))
    nlinarith [hm.2]
  · have ht := b₂ T _ R (W*A) hT ha (by linarith) (mul_nonneg hW hA) f hf
    calc
      _ ≤ C₂*(W*A)*(Real.log T)^2/(1+R)^(p-4) := ht
      _ ≤ C₂*(W*A)*(Real.log T)^2/R^(p-4) := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by linarith) (by linarith) _)
      _ ≤ _ := by apply div_le_div_of_nonneg_right _ (by positivity); nlinarith [mul_nonneg h₁.le (mul_nonneg (mul_nonneg hW hA) (sq_nonneg (Real.log T)))]

end
end HigherCorrelations
