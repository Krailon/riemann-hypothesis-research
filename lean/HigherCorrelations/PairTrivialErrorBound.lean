import HigherCorrelations.PairTrivialCorrection
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! UNCONDITIONAL height decay of the trivial-zero correction. The finite
majorants telescope; no exchange with an improper integral is needed. -/
namespace HigherCorrelations
noncomputable section

theorem pairReciprocalSq_sum_bound (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / (a+(n+1 : ℝ))^2 ≤ 1/a - 1/(a+N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hterm : 1/(a+(N+1:ℝ))^2 ≤ 1/(a+N)-1/(a+(N+1:ℝ)) := by
      field_simp
      nlinarith
    push_cast
    linarith

theorem pairReciprocalSq_tsum_bound (a : ℝ) (ha : 0 < a) :
    ∑' n : ℕ, 1/(a+(n+1:ℝ))^2 ≤ 1/a := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  exact (pairReciprocalSq_sum_bound a ha N).trans (sub_le_self _ (by positivity))

theorem pairCauchy_sum_bound (r : ℝ) (hr : 0 ≤ r) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1/((n+1:ℝ)^2+r^2) ≤ 6/(r+2) := by
  by_cases hsmall : r ≤ 1
  · have hbase : ∀ N : ℕ, ∑ n ∈ Finset.range N, 1/(n+1:ℝ)^2 ≤ 2 := by
      intro N
      cases N with
      | zero => simp
      | succ N =>
        rw [Finset.sum_range_succ']
        have h := pairReciprocalSq_sum_bound 1 (by norm_num) N
        have he : (∑ n ∈ Finset.range N, 1/((n+1:ℕ)+1:ℝ)^2) =
            ∑ n ∈ Finset.range N, 1/(1+(n+1:ℝ))^2 := by
          apply Finset.sum_congr rfl
          intro n hn
          congr 2
          push_cast
          ring
        rw [he]
        norm_num at h ⊢
        have : 0 ≤ (1+(N:ℝ))⁻¹ := by positivity
        linarith
    calc
      _ ≤ ∑ n ∈ Finset.range N, 1/(n+1:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      _ ≤ 2 := hbase N
      _ ≤ 6/(r+2) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  · have hpos : 0 < r := by linarith
    calc
      _ ≤ ∑ n ∈ Finset.range N, 2/(r+(n+1:ℝ))^2 := by
        apply Finset.sum_le_sum
        intro n hn
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [sq_nonneg ((n+1:ℝ)-r)]
      _ = 2 * ∑ n ∈ Finset.range N, 1/(r+(n+1:ℝ))^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ ≤ 2 * (1/r-1/(r+N)) := mul_le_mul_of_nonneg_left
        (pairReciprocalSq_sum_bound r hpos N) (by norm_num)
      _ ≤ 2/r := by
        have : 0 ≤ 1/(r+N) := by positivity
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
          (sub_le_self (1/r) this) (show (0:ℝ) ≤ 2 by norm_num)
      _ ≤ 6/(r+2) := (div_le_div_iff₀ hpos (by positivity)).mpr (by linarith)

theorem pairCauchy_tsum_bound (r : ℝ) (hr : 0 ≤ r) :
    ∑' n : ℕ, 1/((n+1:ℝ)^2+r^2) ≤ 6/(r+2) :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (pairCauchy_sum_bound r hr)

theorem pairTrivialTerm_height_bound (n : ℕ) (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairTrivialTerm n (X,t)‖ ≤
      2 * X^(-5/2 : ℝ) / ((n+1:ℝ)^2+t^2) := by
  have he : ‖Complex.exp ((Real.log X : ℂ) *
      (-2*(n+1:ℂ)-pairSpectralPoint t))‖ ≤ X^(-5/2 : ℝ) := by
    rw [Complex.norm_exp, Real.rpow_def_of_pos (by linarith : 0 < X)]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.sub_re, Complex.neg_re, Complex.add_re,
      Complex.natCast_re, Complex.one_re, 
      Complex.neg_im, Complex.add_im, Complex.natCast_im, Complex.one_im, zero_add, mul_zero]
    have hs : (pairSpectralPoint t).re = 1/2 := by simp [pairSpectralPoint]
    rw [hs]
    norm_num at ⊢
    have hn := Nat.cast_nonneg (α := ℝ) n
    nlinarith [Real.log_nonneg hX, mul_nonneg hn (Real.log_nonneg hX)]
  unfold pairTrivialTerm
  dsimp only [Prod.fst, Prod.snd]
  rw [norm_div, norm_mul, Complex.norm_ofNat]
  calc
    _ ≤ 2 * X^(-5/2 : ℝ) /
        ‖(2*(n+1:ℂ)+pairSpectralPoint t-1)*(2*(n+1:ℂ)+pairSpectralPoint t+1)‖ :=
      div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pairTrivial_denominator_lower n t)

theorem pairTrivialCorrection_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairTrivialCorrection (X,t)‖ ≤ 12 * X^(-5/2 : ℝ) / (|t|+2) := by
  have hs : Summable (fun n : ℕ => 1/((n+1:ℝ)^2+t^2)) := by
    apply summable_of_sum_range_le (fun n => by positivity)
      (c := 6/(|t|+2))
    intro N
    simpa only [sq_abs] using pairCauchy_sum_bound |t| (abs_nonneg t) N
  calc
    _ ≤ ∑' n, ‖pairTrivialTerm n (X,t)‖ :=
      norm_tsum_le_tsum_norm (pairTrivialTerm_summable (X,t) hX)
    _ ≤ ∑' n : ℕ, 2 * X^(-5/2 : ℝ) * (1/((n+1:ℝ)^2+t^2)) := by
      apply Summable.tsum_le_tsum
        (fun n => by simpa [div_eq_mul_inv] using pairTrivialTerm_height_bound n X t hX)
        (pairTrivialTerm_summable (X,t) hX) (hs.mul_left _)
    _ = 2 * X^(-5/2 : ℝ) * ∑' n : ℕ, 1/((n+1:ℝ)^2+t^2) := tsum_mul_left
    _ ≤ 2 * X^(-5/2 : ℝ) * (6/(|t|+2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sq_abs] using pairCauchy_tsum_bound |t| (abs_nonneg t)
    _ = _ := by ring

end
end HigherCorrelations
