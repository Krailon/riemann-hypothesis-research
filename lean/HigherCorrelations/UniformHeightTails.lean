import HigherCorrelations.UniformHeightCounting

/-! UNCONDITIONAL normalized decay estimates from the global count alone. -/
namespace HigherCorrelations
noncomputable section
open scoped Classical

theorem anchoredTailRadius_nonneg (T a R : ℝ) (hR : 0 ≤ R) (t : AnchoredTail T a R) :
    0 ≤ anchoredTailRadius T a R t := div_nonneg (sub_nonneg.mpr t.property) (by positivity)

theorem anchoredTailRadius_identity (T a R : ℝ) (hR : 0 ≤ R) (t : AnchoredTail T a R) :
    (1+R)*(1+anchoredTailRadius T a R t) = 1+anchoredRadius T a t.val := by
  unfold anchoredTailRadius
  field_simp
  <;> ring

theorem anchoredTail_shell_upper (T a R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (t : AnchoredTail T a R) (ht : dyadicIndex (anchoredTailRadius T a R t) = n) :
    anchoredRadius T a t.val ≤ (1+R)*2^(n+1) := by
  have h := (dyadicIndex_bounds _ (anchoredTailRadius_nonneg T a R hR t)).2
  rw [ht] at h
  have hh := mul_lt_mul_of_pos_left h (show 0 < 1+R by positivity)
  rw [anchoredTailRadius_identity T a R hR t] at hh
  linarith

theorem anchoredTail_shell_finite (T a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) (n : ℕ) :
    Set.Finite {t : AnchoredTail T a R | dyadicIndex (anchoredTailRadius T a R t) = n} := by
  apply ((anchoredBall_finite T a ((1+R)*2^(n+1)) ha).preimage Subtype.val_injective.injOn).subset
  intro t ht
  exact anchoredTail_shell_upper T a R hR n t ht

def anchoredTailShells (T a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) : OccurrenceShells (AnchoredTail T a R) where
  shell t := dyadicIndex (anchoredTailRadius T a R t)
  members n := (anchoredTail_shell_finite T a R ha hR n).toFinset
  mem_iff _ _ := Set.Finite.mem_toFinset _

theorem anchoredTail_shell_count :
    ∃ C : ℝ, 0 < C ∧ ∀ T a R : ℝ, uniformHeightThreshold ≤ T →
      ∀ ha : 1 ≤ a, ∀ hR : 0 ≤ R, ∀ n : ℕ,
      (((anchoredTailShells T a R (by linarith) hR).members n).card:ℝ) ≤
        C*T*(Real.log T)^3*(1+R)^4*((2:ℝ)^4)^n := by
  obtain ⟨C,hC,hb⟩ := anchored_count_uniform
  refine ⟨81*C,by positivity,fun T a R hT ha hR n => ?_⟩
  have ha' : 0<a := by linarith
  have ht := (uniformHeightThreshold_bounds hT).1
  have hq := (uniformHeightThreshold_bounds hT).2.1
  have hc : ((anchoredTailShells T a R ha' hR).members n).card ≤
      (anchoredBall T a ((1+R)*2^(n+1))).card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro t ht
      exact (mem_anchoredBall _ _ _ ha' _).mpr (anchoredTail_shell_upper T a R hR n t
        (((anchoredTailShells T a R ha' hR).mem_iff t n).mp ht))
    · exact Subtype.val_injective.injOn
  have hn : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
  have hr : 1+(1+R)*2^(n+1) ≤ 3*(1+R)*2^n := by rw [pow_succ]; nlinarith
  calc
    _ ≤ C*T*(Real.log T)^3*(1+(1+R)*2^(n+1))^4 := (Nat.cast_le.mpr hc).trans (hb T a _ hT ha (by positivity))
    _ ≤ C*T*(Real.log T)^3*(3*(1+R)*2^n)^4 := by gcongr
    _ = _ := by rw [mul_pow,mul_pow,← pow_mul,Nat.mul_comm n 4,pow_mul]; ring

theorem anchoredTail_shell_decay (T a R : ℝ) (ha : 0<a) (hR : 0 ≤ R)
    (f : AnchoredTriple T → ℂ) (A : ℝ) (hA : 0 ≤ A) (p : ℕ)
    (hf : ∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) (t : AnchoredTail T a R) :
    ‖f t.val‖ ≤ (A/(1+R)^p)/((2:ℝ)^p)^(anchoredTailShells T a R ha hR).shell t := by
  have hh := (dyadicIndex_bounds _ (anchoredTailRadius_nonneg T a R hR t)).1
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1+R by positivity)
  rw [anchoredTailRadius_identity T a R hR t] at hm
  have hp := pow_le_pow_left₀ (show 0 ≤ (1+R)*2^dyadicIndex (anchoredTailRadius T a R t) by positivity) hm p
  have he : ((1+R)*2^dyadicIndex (anchoredTailRadius T a R t))^p =
      (1+R)^p*((2:ℝ)^p)^(anchoredTailShells T a R ha hR).shell t := by
    rw [mul_pow,← pow_mul,Nat.mul_comm _ p,pow_mul]; rfl
  rw [he] at hp
  exact (hf t.val).trans (by rw [div_div]; exact div_le_div_of_nonneg_left hA (by positivity) hp)

theorem dyadic_total_bound {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (d p : ℕ) (hp : d<p)
    (hc : ∀ n, ((S.members n).card:ℝ) ≤ C*((2:ℝ)^d)^n)
    (hf : ∀ i, ‖f i‖ ≤ A/((2:ℝ)^p)^S.shell i) :
    Summable (fun i => ‖f i‖) ∧ (∑' i, ‖f i‖) ≤ A*C/(1-dyadicRatio d p) := by
  have hs := dyadic_summable_norm S f A C hA hC d p hp hc hf
  refine ⟨hs,?_⟩
  have hh := dyadic_tail_bound S f A C hA hC d p hp hc hf 0
  let e : I ≃ {i : I // 0 ≤ S.shell i} :=
    { toFun := fun i => ⟨i,Nat.zero_le _⟩
      invFun := fun i => i.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := e.tsum_eq (fun i => ‖f i.val‖)
  simpa [← he,e] using hh

theorem anchored_decay_tail_uniform (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a R A : ℝ, uniformHeightThreshold ≤ T →
      1 ≤ a → 0 ≤ R → 0 ≤ A → ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      Summable (fun t : AnchoredTail T a R => ‖f t.val‖) ∧
      (∑' t : AnchoredTail T a R, ‖f t.val‖)/(T*Real.log T) ≤
        C*A*(Real.log T)^2/(1+R)^(p-4) := by
  obtain ⟨C,hC,hb⟩ := anchoredTail_shell_count
  have hd : 0 < 1-dyadicRatio 4 p := sub_pos.mpr (dyadic_ratio_bounds 4 p hp).2
  refine ⟨C/(1-dyadicRatio 4 p),by positivity,fun T a R A hT ha hR hA f hf => ?_⟩
  have ha' : 0<a := by linarith
  obtain ⟨ht,hq,_⟩ := uniformHeightThreshold_bounds hT
  have hs := dyadic_total_bound (anchoredTailShells T a R ha' hR) (fun t => f t.val)
    (A/(1+R)^p) (C*T*(Real.log T)^3*(1+R)^4) (by positivity) (by positivity)
    4 p hp (hb T a R hT ha hR) (anchoredTail_shell_decay T a R ha' hR f A hA p hf)
  refine ⟨hs.1,?_⟩
  have he : (1+R)^p = (1+R)^(p-4)*(1+R)^4 := by rw [← pow_add,Nat.sub_add_cancel (by omega)]
  calc
    _ ≤ ((A/(1+R)^p)*(C*T*(Real.log T)^3*(1+R)^4)/(1-dyadicRatio 4 p))/(T*Real.log T) :=
      div_le_div_of_nonneg_right hs.2 (by positivity)
    _ = _ := by rw [he]; field_simp

end
end HigherCorrelations
