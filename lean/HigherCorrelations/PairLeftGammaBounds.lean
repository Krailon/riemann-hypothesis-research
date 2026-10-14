import HigherCorrelations.PairDigammaBounds

/-! Bounds uniform in the odd left boundary and its ordinate. UNCONDITIONAL.
The linear loss in M is sufficient for X>1; it is not an effective logarithmic-in-M estimate. -/
namespace HigherCorrelations
noncomputable section
open Complex

private theorem halfInteger_avoid (M n : ℕ) (v : ℝ) :
    (-(M:ℂ)-1/2+(v:ℂ)*I) ≠ -(n:ℂ) := by
  intro he
  have hh := congrArg Complex.re he
  simp at hh
  by_cases hn : n ≤ M
  · have hc : (n:ℝ) ≤ (M:ℝ) := by exact_mod_cast hn
    linarith
  · have hc : (M:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge hn))
    linarith

private theorem inverse_norm_le_of_half_le {z : ℂ} (hz : 1/2 ≤ ‖z‖) : ‖z⁻¹‖ ≤ 2 := by
  simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) hz

theorem pairDigamma_left_uniform : ∃ G : ℝ, 0 < G ∧ ∀ (M : ℕ) (v : ℝ),
    ‖digamma ((-(2*(M:ℂ)+1)+(v:ℂ)*I)/2)‖ +
      ‖digamma ((1-(-(2*(M:ℂ)+1)+(v:ℂ)*I))/2)‖ ≤
        G*Real.log (|v|+2)+3*M+2 := by
  obtain ⟨D,hD,hhalf⟩ := exists_norm_digamma_le_log (a := 1/2) (b := 1/2) (by norm_num)
  obtain ⟨E,hE,hone⟩ := exists_norm_digamma_le_log (a := 1) (b := 1) (by norm_num)
  refine ⟨D+E,by positivity,fun M v => ?_⟩
  let w : ℂ := -(M:ℂ)-1/2+(v/2:ℝ)*I
  let u : ℂ := 1-(v/2:ℝ)*I
  have hw : ∀ n : ℕ, w ≠ -(n:ℂ) := fun n => halfInteger_avoid M n (v/2)
  have hu : ∀ n : ℕ, u ≠ -(n:ℂ) := by
    intro n he
    have hh := congrArg Complex.re he
    simp [u] at hh
    have := Nat.cast_nonneg (α:=ℝ) n
    linarith
  have hwr : w+(M+1:ℕ) = (1/2:ℂ)+(v/2:ℝ)*I := by dsimp [w]; push_cast; ring
  have hur : u+M = (1-(-(2*(M:ℂ)+1)+(v:ℂ)*I))/2 := by
    dsimp [u]; push_cast; ring
  have hwz : w = (-(2*(M:ℂ)+1)+(v:ℂ)*I)/2 := by dsimp [w]; push_cast; ring
  have hlog : Real.log (|v/2|+2) ≤ Real.log (|v|+2) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div]; norm_num
  have hwb := hhalf ((1/2:ℂ)+(v/2:ℝ)*I) (by norm_num) (by norm_num)
  have hub := hone u (by simp [u]) (by simp [u])
  simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero, zero_add] at hwb
  have hwb' : ‖digamma (w+(M+1:ℕ))‖ ≤ D*Real.log (|v|+2) := by
    rw [hwr]
    exact hwb.trans (mul_le_mul_of_nonneg_left hlog hD.le)
  have hub' : ‖digamma u‖ ≤ E*Real.log (|v|+2) := by
    have he : |u.im| = |v/2| := by simp [u]
    rw [he] at hub
    exact hub.trans (mul_le_mul_of_nonneg_left hlog hE.le)
  have hws : ‖∑ k ∈ Finset.range (M+1), (w+(k:ℂ))⁻¹‖ ≤ 2*((M:ℝ)+1) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k ∈ Finset.range (M+1), (2:ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply inverse_norm_le_of_half_le
        have hk' : (k:ℝ) ≤ (M:ℝ) := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
        have hh := Complex.abs_re_le_norm (w+(k:ℂ))
        have hre : (w+(k:ℂ)).re = -(M:ℝ)-1/2+k := by simp [w]
        rw [hre, abs_of_nonpos (by linarith)] at hh
        linarith
      _ = _ := by simp; ring
  have hus : ‖∑ k ∈ Finset.range M, (u+(k:ℂ))⁻¹‖ ≤ (M:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k ∈ Finset.range M, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hh := Complex.abs_re_le_norm (u+(k:ℂ))
        have hre : (u+(k:ℂ)).re = 1+(k:ℝ) := by simp [u]
        rw [hre, abs_of_nonneg (by positivity : 0 ≤ 1+(k:ℝ))] at hh
        have hp : 0 < ‖u+(k:ℂ)‖ := by have := Nat.cast_nonneg (α:=ℝ) k; linarith
        rw [norm_inv, inv_le_one₀ hp]
        have := Nat.cast_nonneg (α:=ℝ) k
        linarith
      _ = _ := by simp
  have hwrec := digamma_apply_add_nat hw (M+1)
  have hurec := digamma_apply_add_nat hu M
  have hwt := norm_sub_le (digamma (w+(M+1:ℕ))) (∑ k ∈ Finset.range (M+1), (w+(k:ℂ))⁻¹)
  have hwt' : ‖digamma w‖ ≤ ‖digamma (w+(M+1:ℕ))‖ +
      ‖∑ k ∈ Finset.range (M+1), (w+(k:ℂ))⁻¹‖ := by
    convert hwt using 1
    rw [hwrec, add_sub_cancel_right]
  have hut : ‖digamma (u+M)‖ ≤ ‖digamma u‖ + ‖∑ k ∈ Finset.range M, (u+(k:ℂ))⁻¹‖ := by
    rw [hurec]
    exact norm_add_le _ _
  rw [← hwz, ← hur]
  linarith

end
end HigherCorrelations
