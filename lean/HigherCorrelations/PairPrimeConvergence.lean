import HigherCorrelations.PairSeriesTopology
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! UNCONDITIONAL prime-series M-test; only absolute L-series convergence is used. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

private def primeMajorant (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (n+1) / (n+1 : ℝ) ^ (3/2 : ℝ)

set_option backward.isDefEq.respectTransparency false in
private theorem primeMajorant_summable : Summable primeMajorant := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (3/2 : ℂ)) (by norm_num)).norm
  have hs := h.comp_injective (fun a b (h : a+1=b+1) => Nat.add_right_cancel h)
  unfold primeMajorant
  convert hs using 1
  ext n
  simp [LSeries.norm_term_eq, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

private theorem primeTerm_norm (n : ℕ) (p : ℝ × ℝ) (hX : 1≤p.1) :
    ‖pairPrimeTerm n p‖ = ArithmeticFunction.vonMangoldt (n+1) *
      Real.exp (Real.log (n+1 : ℝ)*(-(1/2 : ℝ))) * min ((n+1 : ℝ)/p.1) (p.1/(n+1 : ℝ)) := by
  have hx : 0≤p.1 := by linarith
  unfold pairPrimeTerm
  rw [norm_mul, norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    abs_of_nonneg (show 0 ≤ min ((n+1 : ℝ)/p.1) (p.1/(n+1 : ℝ)) by positivity)]

private theorem pairPrimeTerm_bound (n : ℕ) (p : ℝ × ℝ) (B : ℝ)
    (hX : 1≤p.1) (hB : p.1≤B) : ‖pairPrimeTerm n p‖ ≤ B*primeMajorant n := by
  have hn : 0 < (n+1 : ℝ) := by positivity
  have hm : min ((n+1 : ℝ)/p.1) (p.1/(n+1 : ℝ)) ≤ B/(n+1 : ℝ) :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_right hB hn.le)
  rw [primeTerm_norm n p hX]
  calc
    _ ≤ (ArithmeticFunction.vonMangoldt (n+1)*Real.exp (Real.log (n+1 : ℝ)*(-(1/2 : ℝ)))) * (B/(n+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)
    _ = B*primeMajorant n := by
      unfold primeMajorant
      rw [Real.rpow_def_of_pos hn]
      have he : Real.exp (Real.log (n+1 : ℝ)*(3/2 : ℝ)) =
          (n+1 : ℝ)*Real.exp (Real.log (n+1 : ℝ)*(1/2 : ℝ)) := by
        rw [show Real.log (n+1 : ℝ)*(3/2 : ℝ) = Real.log (n+1 : ℝ) + Real.log (n+1 : ℝ)*(1/2 : ℝ) by ring,
          Real.exp_add, Real.exp_log hn]
      rw [he, show Real.log (n+1 : ℝ)*(-(1/2 : ℝ)) = -(Real.log (n+1 : ℝ)*(1/2 : ℝ)) by ring, Real.exp_neg]
      field_simp

theorem pairPrimeTerm_summable (X t : ℝ) (hX : 1≤X) :
    Summable (fun n => ‖pairPrimeTerm n (X,t)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => pairPrimeTerm_bound n (X,t) X hX le_rfl) (primeMajorant_summable.mul_left X)

theorem pairPrime_uniform_rectangle (B H : ℝ) (_hB : 1≤B) :
    TendstoUniformlyOn (fun N : ℕ => fun p => ∑ n ∈ Finset.range N, pairPrimeTerm n p)
      pairPrimeSeries atTop (pairSeriesRectangle B H) := by
  exact tendstoUniformlyOn_tsum_nat (primeMajorant_summable.mul_left B)
    (fun n p hp => pairPrimeTerm_bound n p B hp.1 hp.2.1)

theorem pairPrime_locallyUniform :
    TendstoLocallyUniformlyOn (fun N : ℕ => fun p => ∑ n ∈ Finset.range N, pairPrimeTerm n p)
      pairPrimeSeries atTop pairSeriesDomain :=
  pairSeries_locallyUniform pairPrime_uniform_rectangle

theorem pairPrimeTerm_continuous (n : ℕ) : ContinuousOn (pairPrimeTerm n) pairSeriesDomain := by
  apply ContinuousOn.mul
  · fun_prop
  · apply Complex.continuous_ofReal.comp_continuousOn
    apply ContinuousOn.inf
    · exact continuousOn_const.div continuousOn_fst (fun p hp => by have : 1≤p.1 := hp; linarith)
    · exact continuousOn_fst.div_const _

theorem pairPrimeSeries_continuous : ContinuousOn pairPrimeSeries pairSeriesDomain := by
  apply pairPrime_locallyUniform.continuousOn
  exact Filter.Frequently.of_forall (fun N => continuousOn_finsetSum _ (fun n _ => pairPrimeTerm_continuous n))

theorem pairPrimeTerm_one (p : ℝ × ℝ) : pairPrimeTerm 0 p = 0 := by
  simp [pairPrimeTerm]

end
end HigherCorrelations
