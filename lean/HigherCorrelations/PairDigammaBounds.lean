import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import HigherCorrelations.PairExactDefinitions

/-! Logarithmic digamma bounds on fixed vertical strips, away from the real axis.
UNCONDITIONAL. The constant can depend on the strip and the integer shift. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem pairDigamma_shift_bound (N : ℕ) (a b : ℝ) (ha : 0 < a+N) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖digamma z‖ ≤ C*Real.log (|z.im|+2) := by
  obtain ⟨D,hD,hbound⟩ := exists_norm_digamma_le_log (a := a+N) (b := b+N) ha
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨D+N/Real.log 2,by positivity,fun z hza hzb hzi => ?_⟩
  have hn : ∀ m : ℕ, z ≠ -(m:ℂ) := by
    intro m he
    have hh := congrArg Complex.im he
    simp at hh
    norm_num [hh] at hzi
  have hterm (k : ℕ) : ‖(z+(k:ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, inv_le_one₀]
    · exact hzi.trans (by simpa using Complex.abs_im_le_norm (z+(k:ℂ)))
    · have hh := Complex.abs_im_le_norm (z+(k:ℂ))
      simp only [Complex.add_im, Complex.natCast_im, add_zero] at hh
      linarith
  have hs : ‖∑ k ∈ Finset.range N, (z+(k:ℂ))⁻¹‖ ≤ (N:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k ∈ Finset.range N, (1:ℝ) := Finset.sum_le_sum (fun k _ => hterm k)
      _ = _ := by simp
  have hrec := digamma_apply_add_nat hn N
  have htri := norm_sub_le (digamma (z+N)) (∑ k ∈ Finset.range N, (z+(k:ℂ))⁻¹)
  rw [hrec, add_sub_cancel_right] at htri
  have hb := hbound (z+N) (by simpa using add_le_add_right hza (N:ℝ))
    (by simpa using add_le_add_right hzb (N:ℝ))
  simp only [Complex.add_im, Complex.natCast_im, add_zero] at hb
  rw [hrec] at hb
  have hlog : Real.log 2 ≤ Real.log (|z.im|+2) :=
    Real.log_le_log (by norm_num) (by have := abs_nonneg z.im; linarith)
  have hN : (N:ℝ) ≤ N/Real.log 2*Real.log (|z.im|+2) := by
    have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (N:ℝ)/Real.log 2)
    rwa [div_mul_cancel₀ _ hl2.ne'] at hh
  nlinarith

theorem pairDigamma_horizontal_bound (M : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ σ v : ℝ, -(2*M+1) ≤ σ → σ ≤ 5/2 → 2 ≤ |v| →
      ‖digamma (((σ:ℂ)+(v:ℂ)*I)/2+1)‖ ≤ G*Real.log (|v|+2) := by
  obtain ⟨G,hG,hbound⟩ := pairDigamma_shift_bound (M+1) (-(M:ℝ)+1/2) (9/4)
    (by push_cast; linarith)
  refine ⟨G,hG,fun σ v hlo hhi hv => ?_⟩
  have hre : (((σ:ℂ)+(v:ℂ)*I)/2+1).re = σ/2+1 := by simp
  have him : (((σ:ℂ)+(v:ℂ)*I)/2+1).im = v/2 := by simp
  have hb := hbound (((σ:ℂ)+(v:ℂ)*I)/2+1)
    (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him, abs_div]; norm_num; linarith)
  rw [him] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hG.le
  apply Real.log_le_log (by positivity)
  rw [abs_div]
  norm_num

end
end HigherCorrelations
