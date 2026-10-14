import HigherCorrelations.PairExactDefinitions
import HigherCorrelations.PairSeriesTopology
import Mathlib.Analysis.PSeries

/-! Absolute and uniform convergence of the trivial-zero correction, including X=1.
UNCONDITIONAL. The dominating series is explicit and independent of both X and t. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem pairTrivial_denominator_lower (n : ℕ) (t : ℝ) :
    (n+1 : ℝ)^2 + t^2 ≤
      ‖(2*(n+1 : ℂ) + pairSpectralPoint t - 1) *
        (2*(n+1 : ℂ) + pairSpectralPoint t + 1)‖ := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : ((n+1 : ℝ)^2+t^2)^2 ≤
      ‖(2*(n+1 : ℂ) + pairSpectralPoint t - 1) *
        (2*(n+1 : ℂ) + pairSpectralPoint t + 1)‖^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_mul]
    simp [Complex.normSq_apply, pairSpectralPoint, Complex.mul_re, Complex.mul_im]
    nlinarith [sq_nonneg t, sq_nonneg (n:ℝ), mul_nonneg hn (sq_nonneg t)]
  nlinarith [norm_nonneg ((2*(n+1 : ℂ) + pairSpectralPoint t - 1) *
    (2*(n+1 : ℂ) + pairSpectralPoint t + 1)), sq_nonneg t]

theorem pairTrivial_denominator_ne_zero (n : ℕ) (t : ℝ) :
    (2*(n+1 : ℂ) + pairSpectralPoint t - 1) *
      (2*(n+1 : ℂ) + pairSpectralPoint t + 1) ≠ 0 := by
  intro h
  have hb := pairTrivial_denominator_lower n t
  rw [h, norm_zero] at hb
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [sq_nonneg t]

theorem pairTrivialTerm_bound (n : ℕ) (p : ℝ × ℝ) (hX : 1 ≤ p.1) :
    ‖pairTrivialTerm n p‖ ≤ 2 / (n+1 : ℝ)^2 := by
  have he : ‖Complex.exp ((Real.log p.1 : ℂ) *
      (-2*(n+1 : ℂ) - pairSpectralPoint p.2))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.sub_re, Complex.mul_re, Complex.neg_re,
      Complex.add_re, Complex.natCast_re, Complex.one_re]
    have hs : (pairSpectralPoint p.2).re = 1/2 := by simp [pairSpectralPoint]
    rw [hs]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.log_nonneg hX)
      (by have := Nat.cast_nonneg (α := ℝ) n; norm_num; linarith)
  unfold pairTrivialTerm
  rw [norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ 2 / ‖(2*(n+1 : ℂ) + pairSpectralPoint p.2 - 1) *
        (2*(n+1 : ℂ) + pairSpectralPoint p.2 + 1)‖ :=
      div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ 2 / (n+1 : ℝ)^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      ((le_add_of_nonneg_right (sq_nonneg _)).trans (pairTrivial_denominator_lower n p.2))

private theorem trivialMajorant_summable : Summable (fun n : ℕ => 2 / (n+1 : ℝ)^2) := by
  have h := (Real.summable_nat_pow_inv.mpr (show 1 < 2 by norm_num)).comp_injective
    (fun a b (h : a+1=b+1) => Nat.add_right_cancel h)
  simpa [div_eq_mul_inv] using h.mul_left 2

theorem pairTrivialTerm_summable (p : ℝ × ℝ) (hX : 1 ≤ p.1) :
    Summable (fun n => ‖pairTrivialTerm n p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => pairTrivialTerm_bound n p hX) trivialMajorant_summable

theorem pairTrivial_uniform :
    TendstoUniformlyOn (fun N : ℕ => fun p => ∑ n ∈ Finset.range N, pairTrivialTerm n p)
      pairTrivialCorrection atTop pairSeriesDomain :=
  tendstoUniformlyOn_tsum_nat trivialMajorant_summable
    (fun n p hp => pairTrivialTerm_bound n p hp)

theorem pairTrivialTerm_continuous (n : ℕ) :
    ContinuousOn (pairTrivialTerm n) pairSeriesDomain := by
  apply ContinuousOn.div
  · apply ContinuousOn.const_mul
    apply Complex.continuous_exp.comp_continuousOn
    apply ContinuousOn.mul
    · exact Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_fst.log (fun p hp => by have : 1 ≤ p.1 := hp; linarith))
    · unfold pairSpectralPoint
      fun_prop
  · unfold pairSpectralPoint
    fun_prop
  · exact fun p _ => pairTrivial_denominator_ne_zero n p.2

theorem pairTrivialCorrection_continuous :
    ContinuousOn pairTrivialCorrection pairSeriesDomain := by
  apply pairTrivial_uniform.tendstoLocallyUniformlyOn.continuousOn
  exact Filter.Frequently.of_forall (fun N =>
    continuousOn_finsetSum _ (fun n _ => pairTrivialTerm_continuous n))

end
end HigherCorrelations
