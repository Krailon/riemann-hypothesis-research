import HigherCorrelations.TripleResonanceBalls
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! UNCONDITIONAL decaying resonance bound with an explicit
convergent-series constant. Parameters are fixed before the absolutely convergent cover is summed. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem tripleResonanceDecayConstant_pos : 0 < tripleResonanceDecayConstant := by
  have hG : 0 < ∑' j : ℕ, (j+1:ℝ)^3*(1/4:ℝ)^j := by
    have h := pairDiagonalPower_geometric_summable.le_tsum 0 (fun j _ => by positivity)
    norm_num at h
    linarith
  unfold tripleResonanceDecayConstant
  exact mul_pos (mul_pos (by norm_num) tripleProperPowerConstant_pos) hG

theorem tripleResonanceBall_double_summable (Z : ℝ) (hZ : 1 ≤ Z) :
    Summable (fun q : ℕ × ℕ => tripleResonanceBall Z ((2:ℝ)^q.1*Z) q.2) := by
  have hR (j : ℕ) : 1 ≤ (2:ℝ)^j*Z :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hZ
  have hnon (q : ℕ × ℕ) : 0 ≤ tripleResonanceBall Z ((2:ℝ)^q.1*Z) q.2 :=
    tripleResonanceBall_nonneg _ _ (hR _) _
  have hg : Summable (fun j : ℕ => (8*tripleProperPowerConstant*tripleResonanceScale Z)*
      ((j+1:ℝ)^3*(1/4:ℝ)^j)) := pairDiagonalPower_geometric_summable.mul_left _
  have hr : Summable (fun j : ℕ => ∑' n, tripleResonanceBall Z ((2:ℝ)^j*Z) n) :=
    Summable.of_nonneg_of_le (fun j => tsum_nonneg (fun n => hnon (j,n)))
      (tripleResonanceBall_dyadic_bound Z hZ) hg
  exact (summable_prod_of_nonneg hnon).mpr
    ⟨fun j => tripleResonanceBall_summable Z ((2:ℝ)^j*Z),hr⟩

theorem tripleResonanceMajorant_cover (Z : ℝ) (hZ : 1 ≤ Z) (n : ℕ) :
    tripleResonanceMajorant Z n ≤ ∑' j : ℕ, tripleResonanceBall Z ((2:ℝ)^j*Z) n := by
  have hR (j : ℕ) : 1 ≤ (2:ℝ)^j*Z :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hZ
  by_cases hn : IsPrimePow n ∧ ¬n.Prime
  · obtain ⟨j,hj⟩ := tripleResonanceBall_cover Z hZ n hn
    exact hj.trans (((tripleResonanceBall_double_summable Z hZ).prod_symm.prod_factor n).le_tsum j
      (fun k _ => tripleResonanceBall_nonneg _ _ (hR k) _))
  · rw [tripleResonanceMajorant,if_neg hn]
    exact tsum_nonneg (fun j => tripleResonanceBall_nonneg _ _ (hR j) _)

theorem tripleResonanceMajorant_summable (Z : ℝ) (hZ : 1 ≤ Z) :
    Summable (tripleResonanceMajorant Z) :=
  Summable.of_nonneg_of_le (tripleResonanceMajorant_nonneg Z) (tripleResonanceMajorant_cover Z hZ)
    (tripleResonanceBall_double_summable Z hZ).prod_symm.prod

theorem tripleResonanceMajorant_bound (Z : ℝ) (hZ : 1 ≤ Z) :
    (∑' n : ℕ, tripleResonanceMajorant Z n) ≤ tripleResonanceDecayConstant*tripleResonanceScale Z := by
  have hd := tripleResonanceBall_double_summable Z hZ
  calc
    _ ≤ ∑' n : ℕ, ∑' j : ℕ, tripleResonanceBall Z ((2:ℝ)^j*Z) n :=
      (tripleResonanceMajorant_summable Z hZ).tsum_le_tsum (tripleResonanceMajorant_cover Z hZ) hd.prod_symm.prod
    _ = ∑' j : ℕ, ∑' n : ℕ, tripleResonanceBall Z ((2:ℝ)^j*Z) n :=
      Summable.tsum_comm (f := fun (j n : ℕ) => tripleResonanceBall Z ((2:ℝ)^j*Z) n) hd
    _ ≤ ∑' j : ℕ, (8*tripleProperPowerConstant*tripleResonanceScale Z)*((j+1:ℝ)^3*(1/4:ℝ)^j) :=
      hd.prod.tsum_le_tsum (tripleResonanceBall_dyadic_bound Z hZ)
        (pairDiagonalPower_geometric_summable.mul_left _)
    _ = _ := by rw [tsum_mul_left]; unfold tripleResonanceDecayConstant; ring

theorem tripleResonance_grouped_summable (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    Summable (fun n => tripleArithmeticConvolution X Y n*tripleArithmeticCoefficient (X*Y) n) := by
  have hZ : 1 ≤ X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (tripleArithmeticConvolution_nonneg X Y hX hY n)
    (tripleArithmeticCoefficient_nonneg (X*Y) hZ n)) (tripleResonance_pointwise X Y hX hY)
    (tripleResonanceMajorant_summable (X*Y) hZ)

/-- Explicit, weight-independent decay for the original ordered resonance. -/
theorem triplePrimeResonantMass_decay (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    0 ≤ triplePrimeResonantMass X Y ∧ triplePrimeResonantMass X Y ≤
      tripleResonanceDecayConstant*(Real.log (2*(X*Y))^3/Real.sqrt (X*Y)) := by
  have hZ : 1 ≤ X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  refine ⟨triplePrimeResonantMass_nonneg X Y hX hY,?_⟩
  rw [← tripleArithmeticConvolution_diagonal X Y hX hY]
  exact ((tripleResonance_grouped_summable X Y hX hY).tsum_le_tsum
    (tripleResonance_pointwise X Y hX hY) (tripleResonanceMajorant_summable (X*Y) hZ)).trans
    (tripleResonanceMajorant_bound (X*Y) hZ)

theorem tripleResonanceScale_tendsto : Tendsto tripleResonanceScale atTop (𝓝 0) := by
  have h : Tendsto (fun Z : ℝ => Real.log Z^3/Real.sqrt Z) atTop (𝓝 0) := by
    simpa only [show (3:ℝ)=(3:ℕ) by norm_num,Real.rpow_natCast,Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have hc := h.const_mul 8
  simp only [mul_zero] at hc
  apply squeeze_zero' _ _ hc
  · filter_upwards [eventually_ge_atTop (2:ℝ)] with Z hZ
    have hl : 0 ≤ Real.log (2*Z) := Real.log_nonneg (by linarith)
    unfold tripleResonanceScale; positivity
  · filter_upwards [eventually_ge_atTop (2:ℝ)] with Z hZ
    have hZ0 : 0 < Z := by linarith
    have hl0 : 0 ≤ Real.log (2*Z) := Real.log_nonneg (by linarith)
    have hl : Real.log (2*Z) ≤ 2*Real.log Z := by
      rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hZ0.ne']
      linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) hZ]
    have hp := div_le_div_of_nonneg_right (pow_le_pow_left₀ hl0 hl 3) (Real.sqrt_nonneg Z)
    unfold tripleResonanceScale
    convert hp using 1 <;> ring

/-- Only the product scale must grow; either individual scale may stay at one. -/
theorem triplePrimeResonantMass_uniform_vanishing (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y → R ≤ X*Y → triplePrimeResonantMass X Y < η := by
  have ht := tripleResonanceScale_tendsto.const_mul tripleResonanceDecayConstant
  simp only [mul_zero] at ht
  obtain ⟨R,hR⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hη))
  refine ⟨max 1 R,le_max_left _ _,?_⟩
  intro X Y hX hY hXY
  exact (triplePrimeResonantMass_decay X Y hX hY).2.trans_lt
    (hR (X*Y) ((le_max_right _ _).trans hXY))

end
end HigherCorrelations
