import HigherCorrelations.KernelTailShells

/-! UNCONDITIONAL summability and a uniform translated rational-kernel tail. -/
namespace HigherCorrelations
noncomputable section

theorem kernel_geometric_hasSum :
    HasSum (fun n : ℕ => ((n:ℝ)+3)*(1/2:ℝ)^n) 8 := by
  have h₁ := hasSum_coe_mul_geometric_of_norm_lt_one (r:=(1/2:ℝ)) (by norm_num)
  have h₂ := (hasSum_geometric_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).mul_left 3
  convert h₁.add h₂ using 1 <;> norm_num <;> ring

theorem kernelTail_shell_sum (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀ t a : ℝ, ∀ ha : 0 ≤ a, ∀ n : ℕ,
      (((kernelTailShells t a ha).members n).card:ℝ) ≤
        C*(1+a)*2^n*((n:ℝ)+3)*Real.log (|t|+a+2))
    (t a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (∑ i ∈ (kernelTailShells t a ha).members n, ordinateKernel (t-occurrenceOrdinate i.val)) ≤
      (2*C*Real.log (|t|+a+2)/(1+a))*(((n:ℝ)+3)*(1/2:ℝ)^n) := by
  have ha' : 1+a ≠ 0 := by positivity
  calc
    _ ≤ ∑ _i ∈ (kernelTailShells t a ha).members n, 2/((1+a)^2*(4:ℝ)^n) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [((kernelTailShells t a ha).mem_iff i n).mp hi] using kernelTail_shell_decay t a ha i
    _ = (((kernelTailShells t a ha).members n).card:ℝ)*(2/((1+a)^2*(4:ℝ)^n)) := by simp
    _ ≤ (C*(1+a)*2^n*((n:ℝ)+3)*Real.log (|t|+a+2))*(2/((1+a)^2*(4:ℝ)^n)) :=
      mul_le_mul_of_nonneg_right (hb t a ha n) (by positivity)
    _ = _ := by
      have hp : (2:ℝ)^n/(4:ℝ)^n = (1/2:ℝ)^n := by rw [← div_pow]; norm_num
      field_simp at hp ⊢
      rw [hp]

theorem zeroKernelTail_summable_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t a : ℝ, ∀ _ha : 0 ≤ a,
      Summable (fun i : KernelTailOccurrence t a => ordinateKernel (t-occurrenceOrdinate i.val)) ∧
      zeroKernelTail t a ≤ C*Real.log (|t|+a+2)/(1+a) := by
  obtain ⟨C,hC,hb⟩ := kernelTail_shell_count
  refine ⟨16*C,by positivity,fun t a ha => ?_⟩
  let K := 2*C*Real.log (|t|+a+2)/(1+a)
  have hs := (kernel_geometric_hasSum.mul_left K).summable
  have hf := summable_of_shell_bounds (kernelTailShells t a ha)
    (fun i => ordinateKernel (t-occurrenceOrdinate i.val)) (fun i => ordinateKernel_nonneg _)
    _ hs (kernelTail_shell_sum C hC.le hb t a ha)
  refine ⟨hf,?_⟩
  unfold zeroKernelTail
  rw [shell_tsum_eq (kernelTailShells t a ha) _ hf]
  have hsum : Summable (fun n : ℕ => ∑ i ∈ (kernelTailShells t a ha).members n, ordinateKernel (t-occurrenceOrdinate i.val)) := by
    have hh := (hf.hasSum.tsum_fiberwise (kernelTailShells t a ha).shell).summable
    change Summable (fun n => ∑' i : {i // (kernelTailShells t a ha).shell i = n}, ordinateKernel (t-occurrenceOrdinate i.val.val)) at hh
    exact hh.congr (shell_sum_eq (kernelTailShells t a ha) (fun i => ordinateKernel (t-occurrenceOrdinate i.val)))
  calc
    _ ≤ ∑' n : ℕ, K*(((n:ℝ)+3)*(1/2:ℝ)^n) :=
      hsum.tsum_le_tsum
        (kernelTail_shell_sum C hC.le hb t a ha) hs
    _ = K*8 := (kernel_geometric_hasSum.mul_left K).tsum_eq
    _ = _ := by dsimp [K]; ring

theorem zeroKernel_summable_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Summable (fun i : ZeroOccurrence => ordinateKernel (t-occurrenceOrdinate i)) ∧
      zeroKernelSum t ≤ C*Real.log (|t|+2) := by
  obtain ⟨C,hC,hb⟩ := zeroKernelTail_summable_bound
  refine ⟨C,hC,fun t => ?_⟩
  let e : ZeroOccurrence ≃ KernelTailOccurrence t 0 :=
    { toFun := fun i => ⟨i,abs_nonneg _⟩
      invFun := fun i => i.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hf : Summable (fun i : ZeroOccurrence => ordinateKernel (t-occurrenceOrdinate i)) :=
    e.summable_iff.mpr (hb t 0 (by norm_num)).1
  refine ⟨hf,?_⟩
  have hh := (hb t 0 (by norm_num)).2
  have he := e.tsum_eq (fun i => ordinateKernel (t-occurrenceOrdinate i.val))
  simpa [zeroKernelSum,zeroKernelTail,← he,e] using hh

end
end HigherCorrelations
