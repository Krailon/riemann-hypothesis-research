import HigherCorrelations.KernelTailBounds

/-! UNCONDITIONAL global, distant, exterior and interior rational-kernel estimates.
Subtypes count all zero occurrences; all endpoint conventions occur in the statements. -/
namespace HigherCorrelations
noncomputable section

theorem kernel_restricted_le_tail (t a : ℝ) (ha : 0 ≤ a) (P : ZeroOccurrence → Prop)
    (hP : ∀ i, P i → a ≤ |t-occurrenceOrdinate i|) :
    Summable (fun i : {i // P i} => ordinateKernel (t-occurrenceOrdinate i.val)) ∧
    (∑' i : {i // P i}, ordinateKernel (t-occurrenceOrdinate i.val)) ≤ zeroKernelTail t a := by
  obtain ⟨C,hC,hb⟩ := zeroKernelTail_summable_bound
  let j : {i // P i} → KernelTailOccurrence t a := fun i => ⟨i.val,hP i.val i.property⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (congrArg (fun z : KernelTailOccurrence t a => z.val) h)
  have hs := (hb t a ha).1
  have hf := hs.comp_injective hj
  exact ⟨hf,hf.tsum_le_tsum_of_inj j hj (fun _ _ => ordinateKernel_nonneg _) (fun _ => le_rfl) hs⟩

theorem zeroKernel_distant_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T Z t : ℝ, 3 ≤ T → 2*T ≤ Z → 0 ≤ t → t ≤ T →
      (∑' i : {i : ZeroOccurrence // Z < |occurrenceOrdinate i|}, ordinateKernel (t-occurrenceOrdinate i.val)) ≤
        C*Real.log Z/Z := by
  obtain ⟨C,hC,hb⟩ := zeroKernelTail_summable_bound
  refine ⟨4*C,by positivity,fun T Z t hT hZ ht htT => ?_⟩
  have hz : 0<Z := by linarith
  have hh := kernel_restricted_le_tail t (Z/2) (by positivity) (fun i => Z < |occurrenceOrdinate i|) (by
    intro i hi
    have he : |occurrenceOrdinate i| ≤ |t-occurrenceOrdinate i|+t := by
      have := abs_add_le (occurrenceOrdinate i-t) t
      simpa [abs_sub_comm,abs_of_nonneg ht] using this
    linarith)
  have hl : Real.log (|t|+Z/2+2) ≤ 2*Real.log Z := by
    have h := Real.log_le_log (show 0 < |t|+Z/2+2 by positivity)
      (show |t|+Z/2+2 ≤ Z^2 by rw [abs_of_nonneg ht]; nlinarith)
    simpa [Real.log_pow] using h
  calc
    _ ≤ C*Real.log (|t|+Z/2+2)/(1+Z/2) := hh.2.trans (hb t (Z/2) (by positivity)).2
    _ ≤ C*(2*Real.log Z)/(Z/2) := by
      apply div_le_div₀ (mul_nonneg hC.le (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))) (mul_le_mul_of_nonneg_left hl hC.le) (by positivity) (by linarith)
    _ = _ := by ring

theorem zeroKernel_exterior_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T t : ℝ, 0 ≤ T → 0 ≤ t → t ≤ T →
      (∑' i : {i : ZeroOccurrence // occurrenceOrdinate i ≤ 0 ∨ T < occurrenceOrdinate i},
        ordinateKernel (t-occurrenceOrdinate i.val)) ≤
        C*Real.log (T+2)*(1/(1+t)+1/(1+T-t)) := by
  obtain ⟨C,hC,hb⟩ := zeroKernelTail_summable_bound
  refine ⟨2*C,by positivity,fun T t hT ht htT => ?_⟩
  have hs := (zeroKernel_summable_bound.choose_spec.2 t).1
  have hleft := kernel_restricted_le_tail t t ht (fun i => occurrenceOrdinate i ≤ 0) (by
    intro i hi; rw [abs_of_nonneg (by linarith)]; linarith)
  have hright := kernel_restricted_le_tail t (T-t) (by linarith) (fun i => T < occurrenceOrdinate i) (by
    intro i hi; rw [abs_of_nonpos (by linarith)]; linarith)
  have hl : Real.log (|t|+t+2) ≤ 2*Real.log (T+2) := by
    have hh := Real.log_le_log (show 0 < |t|+t+2 by positivity)
      (show |t|+t+2 ≤ (T+2)^2 by rw [abs_of_nonneg ht]; nlinarith)
    simpa [Real.log_pow] using hh
  have hr : Real.log (|t|+(T-t)+2) = Real.log (T+2) := by rw [abs_of_nonneg ht]; congr 1; ring
  have hsum : (∑' i : {i : ZeroOccurrence // occurrenceOrdinate i ≤ 0 ∨ T < occurrenceOrdinate i}, ordinateKernel (t-occurrenceOrdinate i.val)) ≤
      (∑' i : {i : ZeroOccurrence // occurrenceOrdinate i ≤ 0}, ordinateKernel (t-occurrenceOrdinate i.val)) +
      (∑' i : {i : ZeroOccurrence // T < occurrenceOrdinate i}, ordinateKernel (t-occurrenceOrdinate i.val)) := by
    classical
    have he (P : ZeroOccurrence → Prop) :
        (∑' i : {i // P i}, ordinateKernel (t-occurrenceOrdinate i.val)) =
          ∑' i, Set.indicator {i | P i} (fun i => ordinateKernel (t-occurrenceOrdinate i)) i :=
      tsum_subtype {i | P i} (fun i => ordinateKernel (t-occurrenceOrdinate i))
    rw [he,he,he]
    rw [← (hs.indicator {i | occurrenceOrdinate i ≤ 0}).tsum_add (hs.indicator {i | T < occurrenceOrdinate i})]
    apply (hs.indicator {i | occurrenceOrdinate i ≤ 0 ∨ T < occurrenceOrdinate i}).tsum_le_tsum _
      ((hs.indicator {i | occurrenceOrdinate i ≤ 0}).add (hs.indicator {i | T < occurrenceOrdinate i}))
    intro i
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
    split_ifs <;> first | tauto | linarith [ordinateKernel_nonneg (t-occurrenceOrdinate i)]
  have h₁ := hleft.2.trans (hb t t ht).2
  have h₂ := hright.2.trans (hb t (T-t) (by linarith)).2
  rw [hr] at h₂
  have h₃ : C*Real.log (|t|+t+2)/(1+t) ≤ C*(2*Real.log (T+2))/(1+t) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hC.le) (by positivity)
  have hlog : 0 ≤ Real.log (T+2) := Real.log_nonneg (by linarith)
  calc
    _ ≤ C*(2*Real.log (T+2))/(1+t)+C*Real.log (T+2)/(1+(T-t)) := hsum.trans (add_le_add (h₁.trans h₃) h₂)
    _ ≤ _ := by
      have hp : 0 ≤ C*Real.log (T+2)/(1+T-t) := div_nonneg (mul_nonneg hC.le hlog) (by linarith)
      have he : 1+(T-t)=1+T-t := by ring
      rw [he]
      simp only [div_eq_mul_inv] at hp ⊢
      nlinarith [hp]

theorem heightIntervalDistance_geometry (T t : ℝ) (hT : 0 ≤ T) (ht : t ≤ 0 ∨ T ≤ t) :
    0 ≤ heightIntervalDistance T t ∧ |t| ≤ T+heightIntervalDistance T t ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ T → heightIntervalDistance T t ≤ |t-x| := by
  rcases ht with ht|ht
  · have he : heightIntervalDistance T t = -t := by
      unfold heightIntervalDistance
      rw [max_eq_left (show t-T ≤ -t by linarith),max_eq_right (by linarith)]
    rw [he,abs_of_nonpos ht]
    refine ⟨by linarith,by linarith,fun x hx hxT => ?_⟩
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have he : heightIntervalDistance T t = t-T := by
      unfold heightIntervalDistance
      rw [max_eq_right (show -t ≤ t-T by linarith),max_eq_right (by linarith)]
    rw [he,abs_of_nonneg (hT.trans ht)]
    refine ⟨by linarith,by linarith,fun x hx hxT => ?_⟩
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem zeroKernel_interior_finite (T t : ℝ) :
    (∑' i : {i : ZeroOccurrence // 0 < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T},
      ordinateKernel (t-occurrenceOrdinate i.val)) ≤
      ∑ i ∈ occurrenceInterval 0 T, ordinateKernel (t-occurrenceOrdinate i) := by
  have hs := (zeroKernel_summable_bound.choose_spec.2 t).1
  have hf := hs.subtype (fun i => 0 < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T)
  classical
  have he (P : ZeroOccurrence → Prop) :
      (∑' i : {i // P i}, ordinateKernel (t-occurrenceOrdinate i.val)) =
        ∑' i, Set.indicator {i | P i} (fun i => ordinateKernel (t-occurrenceOrdinate i)) i := tsum_subtype {i | P i} (fun i => ordinateKernel (t-occurrenceOrdinate i))
  rw [he]
  have hh : (∑' i, Set.indicator {i : ZeroOccurrence | 0 ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T}
      (fun i => ordinateKernel (t-occurrenceOrdinate i)) i) =
      ∑ i ∈ occurrenceInterval 0 T, ordinateKernel (t-occurrenceOrdinate i) := by
    rw [← he]
    have hp : {i : ZeroOccurrence | 0 ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T} = (occurrenceInterval 0 T : Set ZeroOccurrence) := by
      ext i; exact (mem_occurrenceInterval _ _ _).symm
    change (∑' i : {i : ZeroOccurrence | 0 ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T}, ordinateKernel (t-occurrenceOrdinate i.val)) = _
    rw [hp]
    exact (occurrenceInterval 0 T).tsum_subtype (fun i => ordinateKernel (t-occurrenceOrdinate i))
  rw [← hh]
  apply (hs.indicator _).tsum_le_tsum _ (hs.indicator _)
  intro i
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  split_ifs <;> grind [ordinateKernel_nonneg]

theorem zeroKernel_interior_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T t : ℝ, 3 ≤ T → (t ≤ 0 ∨ T ≤ t) →
      (∑' i : {i : ZeroOccurrence // 0 < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T},
        ordinateKernel (t-occurrenceOrdinate i.val)) ≤
        C*Real.log (T+2)/(1+heightIntervalDistance T t) := by
  obtain ⟨C,hC,hb⟩ := zeroKernelTail_summable_bound
  obtain ⟨D,hD,hd⟩ := occurrence_count_interval
  refine ⟨2*C+2*D,by positivity,fun T t hT ht => ?_⟩
  obtain ⟨ha,hat,hgap⟩ := heightIntervalDistance_geometry T t (by linarith) ht
  let a := heightIntervalDistance T t
  have hlog : 0 ≤ Real.log (T+2) := Real.log_nonneg (by linarith)
  have hmajor (K : ℝ) (hK : K ≤ 2*C+2*D) : K*Real.log (T+2)/(1+a) ≤ (2*C+2*D)*Real.log (T+2)/(1+a) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK hlog) (by dsimp [a]; positivity)
  by_cases hn : a ≤ T
  · have hh := kernel_restricted_le_tail t a ha (fun i => 0 < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T) (fun i hi => hgap _ hi.1.le hi.2)
    have hl : Real.log (|t|+a+2) ≤ 2*Real.log (T+2) := by
      have hh := Real.log_le_log (show 0 < |t|+a+2 by positivity)
        (show |t|+a+2 ≤ (T+2)^2 by change |t| ≤ T+a at hat; nlinarith)
      simpa [Real.log_pow] using hh
    calc
      _ ≤ C*Real.log (|t|+a+2)/(1+a) := hh.2.trans (hb t a ha).2
      _ ≤ (2*C)*Real.log (T+2)/(1+a) := div_le_div_of_nonneg_right (by nlinarith) (by positivity)
      _ ≤ _ := hmajor _ (by linarith)
  · have han : T ≤ a := le_of_not_ge hn
    have hc := hd 0 T (by linarith)
    simp only [abs_zero,abs_of_nonneg (show 0≤T by linarith),max_eq_right (show 0≤T by linarith),sub_zero] at hc
    have hpoint (i : ZeroOccurrence) (hi : i ∈ occurrenceInterval 0 T) :
        ordinateKernel (t-occurrenceOrdinate i) ≤ 1/(1+a^2) := by
      have hh := (mem_occurrenceInterval _ _ i).mp hi
      have hg := hgap _ hh.1 hh.2
      unfold ordinateKernel
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [sq_abs (t-occurrenceOrdinate i)]
    have hr : (T+1)/(1+a^2) ≤ 2/(1+a) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (show 0≤a-T by linarith) (show 0≤1+a by positivity)]
    calc
      _ ≤ ∑ i ∈ occurrenceInterval 0 T, ordinateKernel (t-occurrenceOrdinate i) := zeroKernel_interior_finite T t
      _ ≤ ∑ _i ∈ occurrenceInterval 0 T, 1/(1+a^2) := Finset.sum_le_sum hpoint
      _ = ((occurrenceInterval 0 T).card:ℝ)/(1+a^2) := by simp [div_eq_mul_inv]
      _ ≤ D*(T+1)*Real.log (T+2)/(1+a^2) := div_le_div_of_nonneg_right hc (by positivity)
      _ = (D*Real.log (T+2))*((T+1)/(1+a^2)) := by ring
      _ ≤ (D*Real.log (T+2))*(2/(1+a)) := mul_le_mul_of_nonneg_left hr (mul_nonneg hD.le hlog)
      _ = (2*D)*Real.log (T+2)/(1+a) := by ring
      _ ≤ _ := hmajor _ (by linarith)

end
end HigherCorrelations
