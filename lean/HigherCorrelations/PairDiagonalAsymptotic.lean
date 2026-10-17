import HigherCorrelations.PairDiagonalFinite

/-! UNCONDITIONAL. Uniform diagonal asymptotic for the actual prime coefficients.
All limits below hold with X fixed. Constants are existential. -/
namespace HigherCorrelations
noncomputable section
open Finset Filter
open scoped Topology ArithmeticFunction.vonMangoldt

theorem pairDiagonal_boundary_tendsto (X : ℝ) :
    Tendsto (fun Y : ℝ => X^2*(2*Real.log Y+3)/(4*Y^2)) atTop (nhds 0) := by
  have hl : Tendsto (fun Y : ℝ => Real.log Y/Y^2) atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_atTop (show (0:ℝ)<(2:ℕ) by norm_num)).tendsto_div_nhds_zero
  have hi : Tendsto (fun Y : ℝ => 3/Y^2) atTop (nhds 0) :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).const_div_atTop 3
  convert ((hl.const_mul 2).add hi).const_mul (X^2/4) using 1
  · funext Y; ring
  · ring

theorem pairDiagonal_partial_tendsto (X : ℝ) (hX : 1 ≤ X) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 0 N, pairDiagonalWeight X n*(Λ n)^2)
      atTop (nhds (pairMeanPrimeDiagonal X)) := by
  rw [pairMeanPrimeDiagonal_weight X hX]
  have ht := (pairDiagonalWeight_summable X hX).hasSum.tendsto_sum_nat
  have hn : Tendsto (fun N : ℕ => N+1) atTop atTop := by
    exact tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  convert ht.comp hn using 1
  funext N
  dsimp only [Function.comp_apply]
  rw [Nat.range_succ_eq_Icc_zero]

theorem pairMeanPrimeDiagonal_model_bound : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    |pairMeanPrimeDiagonal X-(Real.log X+1-1/(4*X^2))| ≤ C := by
  obtain ⟨K,hK,hE⟩ := pairDiagonalCumulative_bound
  refine ⟨3*K, by positivity, ?_⟩
  intro X hX
  have ht := (pairDiagonal_boundary_tendsto X).comp tendsto_natCast_atTop_atTop
  have hs := pairDiagonal_partial_tendsto X hX
  have he := (hs.sub ((tendsto_const_nhds (x := Real.log X+1-1/(4*X^2))).sub ht)).abs
  have hb : ∀ᶠ N : ℕ in atTop,
      |(∑ n ∈ Icc 0 N, pairDiagonalWeight X n*(Λ n)^2)-
        (Real.log X+1-1/(4*X^2)-X^2*(2*Real.log (N:ℝ)+3)/(4*(N:ℝ)^2))| ≤ 3*K := by
    filter_upwards [((tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop X))] with N hN
    simpa using pairDiagonal_finite_error_bound K X N hK hX hN hE
  simpa using le_of_tendsto he hb

/-- The requested uniform O(1) remainder, with no unproved PNT premise. -/
theorem pairMeanPrimeDiagonal_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    |pairMeanPrimeDiagonal X-Real.log X| ≤ C := by
  obtain ⟨K,hK,hbound⟩ := pairMeanPrimeDiagonal_model_bound
  refine ⟨K+1, by positivity, ?_⟩
  intro X hX
  have hX0 : 0 < X := by linarith
  have hi : 0 ≤ 1/(4*X^2) := by positivity
  have hi1 : 1/(4*X^2) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hb : |(Real.log X+1-1/(4*X^2))-Real.log X| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  exact (abs_sub_le _ _ _).trans (add_le_add (hbound X hX) hb)

theorem pairMeanPrimeDiagonal_upper : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    pairMeanPrimeDiagonal X ≤ C*Real.log (2*X) := by
  obtain ⟨K,hK,hbound⟩ := pairMeanPrimeDiagonal_asymptotic
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1+K/Real.log 2, by positivity, ?_⟩
  intro X hX
  have hX0 : 0 < X := by linarith
  have hlog := Real.log_nonneg hX
  have hbound' := (abs_le.mp (hbound X hX)).2
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hX0.ne']
  have he : K/Real.log 2*Real.log 2 = K := div_mul_cancel₀ K hlog2.ne'
  have hp : 0 ≤ K/Real.log 2*Real.log X := by positivity
  nlinarith

end
end HigherCorrelations
