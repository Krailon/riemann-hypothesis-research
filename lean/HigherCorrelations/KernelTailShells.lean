import HigherCorrelations.IntervalZeroCounting
import HigherCorrelations.ZeroOccurrenceShells
import HigherCorrelations.UniformHeightDefinitions

/-! UNCONDITIONAL scaled dyadic shells for the rational ordinate kernel. -/
namespace HigherCorrelations
noncomputable section
open scoped Classical

theorem kernelTailRadius_nonneg (t a : ℝ) (ha : 0 ≤ a) (i : KernelTailOccurrence t a) :
    0 ≤ kernelTailRadius t a i := div_nonneg (sub_nonneg.mpr i.property) (by positivity)

theorem kernelTailRadius_identity (t a : ℝ) (ha : 0 ≤ a) (i : KernelTailOccurrence t a) :
    (1+a)*(1+kernelTailRadius t a i) = 1+|t-occurrenceOrdinate i.val| := by
  unfold kernelTailRadius
  field_simp
  <;> ring

theorem kernelTail_shell_upper (t a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (i : KernelTailOccurrence t a) (hi : dyadicIndex (kernelTailRadius t a i) = n) :
    |t-occurrenceOrdinate i.val| ≤ (1+a)*2^(n+1) := by
  have h := (dyadicIndex_bounds _ (kernelTailRadius_nonneg t a ha i)).2
  rw [hi] at h
  have hh := mul_lt_mul_of_pos_left h (show 0 < 1+a by positivity)
  rw [kernelTailRadius_identity t a ha i] at hh
  linarith

theorem kernelTail_shell_finite (t a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Set.Finite {i : KernelTailOccurrence t a | dyadicIndex (kernelTailRadius t a i) = n} := by
  let r := (1+a)*2^(n+1)
  apply ((occurrenceInterval (t-r) (t+r)).finite_toSet.preimage Subtype.val_injective.injOn).subset
  intro i hi
  change i.val ∈ occurrenceInterval (t-r) (t+r)
  apply (mem_occurrenceInterval _ _ _).mpr
  have hh := abs_le.mp (kernelTail_shell_upper t a ha n i hi)
  exact ⟨by dsimp [r]; linarith,by dsimp [r]; linarith⟩

def kernelTailShells (t a : ℝ) (ha : 0 ≤ a) : OccurrenceShells (KernelTailOccurrence t a) where
  shell i := dyadicIndex (kernelTailRadius t a i)
  members n := (kernelTail_shell_finite t a ha n).toFinset
  mem_iff _ _ := Set.Finite.mem_toFinset _

theorem kernelTail_shell_card (t a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ((kernelTailShells t a ha).members n).card ≤
      (occurrenceInterval (t-(1+a)*2^(n+1)) (t+(1+a)*2^(n+1))).card := by
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro i hi
    have hh := abs_le.mp (kernelTail_shell_upper t a ha n i
      (((kernelTailShells t a ha).mem_iff i n).mp hi))
    exact (mem_occurrenceInterval _ _ _).mpr ⟨by linarith,by linarith⟩
  · exact Subtype.val_injective.injOn

theorem kernelTail_shell_log (t a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Real.log (|t|+(1+a)*2^(n+1)+2) ≤ ((n:ℝ)+3)*Real.log (|t|+a+2) := by
  have hn : (1:ℝ) ≤ 2^(n+1) := one_le_pow₀ (by norm_num)
  have hh : |t|+(1+a)*2^(n+1)+2 ≤ (|t|+a+2)*2^(n+2) := by
    simp only [show n+2=(n+1)+1 by omega,pow_succ] at hn ⊢
    nlinarith [abs_nonneg t,mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hn),mul_nonneg ha (sub_nonneg.mpr hn)]
  have hl := Real.log_le_log (show 0 < |t|+(1+a)*2^(n+1)+2 by positivity) hh
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hl
  have hb : Real.log 2 ≤ Real.log (|t|+a+2) := Real.log_le_log (by norm_num) (by have := abs_nonneg t; linarith)
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ (n:ℝ)+2 by positivity)
  push_cast at hl
  nlinarith

theorem kernelTail_shell_count :
    ∃ C : ℝ, 0 < C ∧ ∀ t a : ℝ, ∀ ha : 0 ≤ a, ∀ n : ℕ,
      (((kernelTailShells t a ha).members n).card:ℝ) ≤
        C*(1+a)*2^n*((n:ℝ)+3)*Real.log (|t|+a+2) := by
  obtain ⟨C,hC,hb⟩ := occurrence_count_centered
  refine ⟨3*C,by positivity,fun t a ha n => ?_⟩
  have hn : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
  have hh := (Nat.cast_le (α:=ℝ)).mpr (kernelTail_shell_card t a ha n)
  have hl : 0 ≤ Real.log (|t|+a+2) := Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hm : 1+(1+a)*2^(n+1) ≤ 3*(1+a)*2^n := by rw [pow_succ]; nlinarith
  calc
    _ ≤ C*(1+(1+a)*2^(n+1))*Real.log (|t|+(1+a)*2^(n+1)+2) := hh.trans (hb t _ (by positivity))
    _ ≤ C*(3*(1+a)*2^n)*(((n:ℝ)+3)*Real.log (|t|+a+2)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hm hC.le) (kernelTail_shell_log t a ha n)
      · apply Real.log_nonneg
        have hh : 0 ≤ (1+a)*2^(n+1) := by positivity
        linarith [abs_nonneg t]
      · positivity
    _ = _ := by ring

theorem ordinateKernel_nonneg (x : ℝ) : 0 ≤ ordinateKernel x := by unfold ordinateKernel; positivity

theorem ordinateKernel_quadratic (x : ℝ) : ordinateKernel x ≤ 2/(1+|x|)^2 := by
  unfold ordinateKernel
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_abs x,sq_nonneg (|x|-1)]

theorem kernelTail_shell_decay (t a : ℝ) (ha : 0 ≤ a) (i : KernelTailOccurrence t a) :
    ordinateKernel (t-occurrenceOrdinate i.val) ≤
      2/((1+a)^2*(4:ℝ)^(kernelTailShells t a ha).shell i) := by
  have hh := (dyadicIndex_bounds _ (kernelTailRadius_nonneg t a ha i)).1
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1+a by positivity)
  rw [kernelTailRadius_identity t a ha i] at hm
  have hp := pow_le_pow_left₀ (show 0 ≤ (1+a)*2^dyadicIndex (kernelTailRadius t a i) by positivity) hm 2
  have he : ((1+a)*2^dyadicIndex (kernelTailRadius t a i))^2 =
      (1+a)^2*(4:ℝ)^(kernelTailShells t a ha).shell i := by
    rw [mul_pow,← pow_mul, Nat.mul_comm _ 2,pow_mul]; norm_num [kernelTailShells]
  rw [he] at hp
  exact (ordinateKernel_quadratic _).trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hp)

end
end HigherCorrelations
