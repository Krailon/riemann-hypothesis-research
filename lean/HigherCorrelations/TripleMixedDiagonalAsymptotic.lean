import HigherCorrelations.TripleMixedDiagonalFinite

/-! UNCONDITIONAL. The cutoff tends to infinity with a,b fixed. The error constant
is chosen before both scales; the checked PNT input is existential. -/
namespace HigherCorrelations
noncomputable section
open Finset Filter
open scoped Topology ArithmeticFunction.vonMangoldt

theorem tripleMixedDiagonal_boundary_tendsto (a b : ℝ) :
    Tendsto (fun Y : ℝ => a*b*(2*Real.log Y+3)/(4*Y^2)) atTop (nhds 0) := by
  have hl : Tendsto (fun Y : ℝ => Real.log Y/Y^2) atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_atTop (show (0:ℝ)<(2:ℕ) by norm_num)).tendsto_div_nhds_zero
  have hi : Tendsto (fun Y : ℝ => 3/Y^2) atTop (nhds 0) :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).const_div_atTop 3
  convert ((hl.const_mul 2).add hi).const_mul (a*b/4) using 1
  · funext Y; ring
  · ring

theorem tripleMixedDiagonal_model_bound_of_cumulative (K a b : ℝ) (hK : 0 < K)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ K*u) :
    |tripleBudgetDiagonal a b-tripleMixedDiagonalModel a b| ≤ K*(a/b)*(3+Real.log (b/a)) := by
  have ht := (tripleMixedDiagonal_boundary_tendsto a b).comp tendsto_natCast_atTop_atTop
  have hs := tripleMixedDiagonal_partial_tendsto a b ha hab
  have he := (hs.sub ((tendsto_const_nhds (x := tripleMixedDiagonalModel a b)).sub ht)).abs
  have hb : ∀ᶠ N : ℕ in atTop,
      |(∑ n ∈ Icc 0 N, tripleMixedDiagonalWeight a b n*(Λ n)^2)-
        (tripleMixedDiagonalModel a b-a*b*(2*Real.log (N:ℝ)+3)/(4*(N:ℝ)^2))| ≤
        K*(a/b)*(3+Real.log (b/a)) := by
    filter_upwards [((tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop b))] with N hN
    simpa using tripleMixedDiagonal_finite_error_bound K a b N hK ha hab hN hE
  simpa using le_of_tendsto he hb

theorem tripleMixedDiagonal_model_correction (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |tripleMixedDiagonalModel a b-tripleMixedDiagonalMain a b| ≤ (a/b)*(1+Real.log (b/a)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hlog : 0 ≤ Real.log (b/a) := Real.log_nonneg ((one_le_div ha0).mpr hab)
  have hfrac : 1/(4*a*b) ≤ a/b := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*a*b) hb0).mpr
    have hsq : 1 ≤ a^2 := by nlinarith
    nlinarith [mul_nonneg hb0.le (show 0 ≤ 4*a^2-1 by nlinarith)]
  have hp : 0 ≤ a/b*Real.log (b/a) := mul_nonneg (by positivity) hlog
  have hi : 0 ≤ 1/(4*a*b) := by positivity
  unfold tripleMixedDiagonalModel
  rw [abs_of_nonneg (by nlinarith)]
  linarith

/-- Explicit dependence on the cumulative constant, uniform in both scales. -/
theorem tripleMixedDiagonal_asymptotic_of_cumulative (K : ℝ) (hK : 0 < K)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ K*u)
    (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |tripleBudgetDiagonal a b-tripleMixedDiagonalMain a b| ≤
      (3*K+1)*(a/b)*(1+Real.log (b/a)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hm := tripleMixedDiagonal_model_bound_of_cumulative K a b hK ha hab hE
  have hc := tripleMixedDiagonal_model_correction a b ha hab
  have hl : 0 ≤ Real.log (b/a) := Real.log_nonneg ((one_le_div (by linarith : 0 < a)).mpr hab)
  calc
    _ ≤ |tripleBudgetDiagonal a b-tripleMixedDiagonalModel a b|+
        |tripleMixedDiagonalModel a b-tripleMixedDiagonalMain a b| := abs_sub_le _ _ _
    _ ≤ K*(a/b)*(3+Real.log (b/a))+(a/b)*(1+Real.log (b/a)) := add_le_add hm hc
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ K*(a/b) by positivity) hl]

/-- No arithmetic hypothesis remains: the checked PNT bound discharges it. -/
theorem tripleMixedDiagonal_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ,
    1 ≤ a → a ≤ b →
    |tripleBudgetDiagonal a b-a/(2*b)*(1+Real.log (b/a))*Real.log (a*b)| ≤
      C*(a/b)*(1+Real.log (b/a)) := by
  obtain ⟨K,hK,hE⟩ := pairDiagonalCumulative_bound
  exact ⟨3*K+1, by positivity, fun a b ha hab =>
    tripleMixedDiagonal_asymptotic_of_cumulative K hK hE a b ha hab⟩

/-- Symmetric public interface; no argument-order assumption is needed. -/
theorem tripleMixedDiagonal_asymptotic_symmetric : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ,
    1 ≤ a → 1 ≤ b →
    |tripleBudgetDiagonal a b-tripleMixedDiagonalMain (min a b) (max a b)| ≤
      C*(min a b/max a b)*(1+Real.log (max a b/min a b)) := by
  obtain ⟨C,hC,h⟩ := tripleMixedDiagonal_asymptotic
  refine ⟨C,hC,?_⟩
  intro a b ha hb
  rcases le_total a b with hab | hba
  · simpa only [min_eq_left hab, max_eq_right hab, tripleMixedDiagonalMain] using h a b ha hab
  · rw [tripleBudgetDiagonal_swap a b]
    simpa only [min_eq_right hba, max_eq_left hba, tripleMixedDiagonalMain] using h b a hb hba

end
end HigherCorrelations
