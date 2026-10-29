import HigherCorrelations.TripleQuadrantMainBound
import HigherCorrelations.TripleQuadrantAssembly
import HigherCorrelations.TripleBoundaryUniform

/-! UNCONDITIONAL normalized residual. Integrability precedes every split. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrant_indicator_integral (ψ f : ℝ × ℝ → ℂ) :
    (∫ p, tripleQuadrantAmplitude ψ p*f p) = ∫ p in tripleQuadrant, ψ p*f p := by
  rw [← integral_indicator tripleQuadrant_measurable]
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hp : p ∈ tripleQuadrant <;> simp [tripleQuadrantAmplitude,hp]

theorem tripleQuadrant_main_integrable (ω : ℝ → ℝ) (T B : ℝ) (hB : 0 < B)
    (ψ : ℝ × ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun p => tripleQuadrantAmplitude ψ p*(tripleRetainedMain ω T (B^p.1) (B^p.2):ℂ)) := by
  have hm : Continuous (fun p : ℝ × ℝ => (tripleRetainedMain ω T (B^p.1) (B^p.2):ℂ)) := by
    simp_rw [tripleBoundary_main_frequency ω T B hB]
    apply Complex.continuous_ofReal.comp
    exact ((by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Real.log T^3*Real.exp (-(2*Real.log B*(p.1+p.2))))).add
      (((tripleQuadrantAxisKernel_continuous _).add
        ((tripleQuadrantAxisKernel_continuous _).comp (continuous_snd.prodMk continuous_fst))).const_mul _))
  have hi := ((hψ.mul hm).integrable_of_hasCompactSupport (μ := volume) hc.mul_right).indicator tripleQuadrant_measurable
  convert hi using 1
  funext p
  by_cases hp : p ∈ tripleQuadrant <;> simp [tripleQuadrantAmplitude,hp]

theorem tripleQuadrant_residual_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (κ T : ℝ) (hκ : 0 < κ) (hT : 2*Real.pi < T)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-κ) :
    tripleQuadrantStatistic ω ψ T -
      (∫ p in tripleQuadrant, ψ p*(tripleRetainedMain ω T
        ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2):ℂ))/(Real.log T:ℂ) =
      (∫ p, tripleQuadrantAmplitude ψ p*tripleQuadrantRemainder ω T
        ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2))/(Real.log T:ℂ) := by
  have hi := tripleQuadrant_frequency_integrable ω hω ψ hψ hc κ T hκ hT hs
  have hj := tripleQuadrant_main_integrable ω T _
    (lt_trans zero_lt_one (tripleTestBase_bounds T hT).2.1) ψ hψ.continuous hc
  rw [tripleQuadrantStatistic,tripleQuadrant_identity ω hω ψ hψ hc κ T hκ hT hs,
    ← tripleQuadrant_indicator_integral,← sub_div]
  congr 1
  unfold tripleQuadrantRemainder
  simp_rw [mul_sub]
  rw [integral_sub hi hj]

private theorem normalize_residual (b q L K P : ℝ) (hb : 0 < b) (hbq : b ≤ q)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hP : 0 ≤ P) (hLK : L ≤ K*q) :
    (1+P*L^4)/q ≤ (1+K)*(1/b+P*L^3) := by
  have hq : 0 < q := hb.trans_le hbq
  have h1 : 1/q ≤ 1/b := one_div_le_one_div_of_le hb hbq
  have h2 : L/q ≤ K := (div_le_iff₀ hq).mpr hLK
  calc
    _ = 1/q+(P*L^3)*(L/q) := by ring
    _ ≤ 1/b+(P*L^3)*K := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ ≤ _ := by nlinarith only [mul_nonneg hK (show 0 ≤ 1/b by positivity),mul_nonneg hP (pow_nonneg hL 3)]

theorem tripleQuadrant_residual_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W : ℝ, 0 ≤ W → (∀ u, ω u ≤ W) →
    ∀ (ψ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∀ T κ : ℝ, 2*Real.pi*Real.exp 1 ≤ T → 0 < κ →
    (∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-κ) →
    ‖tripleQuadrantStatistic ω ψ T -
      (∫ p in tripleQuadrant, ψ p*(tripleRetainedMain ω T
        ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2):ℂ))/(Real.log T:ℂ)‖ ≤
      C*tripleQuadrantN1 ψ*(1+W+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) := by
  obtain ⟨A,hA,ha⟩ := tripleBoundary_uniform_integrated
  let K := tripleBoundaryLogConstant
  have hK : 0 < K := tripleBoundaryLogConstant_pos
  refine ⟨A*(1+K),by positivity,?_⟩
  intro ω hω W hW hw ψ hψ hc T κ hT hκ hs
  have ht := tripleBoundary_height T hT
  have hb : 0 < Real.log (tripleTestBase T) := by linarith [ht.2.1]
  have hbq : Real.log (tripleTestBase T) ≤ Real.log T := by
    rw [ht.2.2.1]
    linarith [Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])]
  have hq : 0 < Real.log T := hb.trans_le hbq
  have hL : 0 ≤ Real.log (2*T+2) := le_trans (by norm_num)
    (tripleBudget_height_log T (tripleTestBase_bounds T ht.1).1)
  have hp : 0 ≤ (tripleTestBase T)^(-κ) := Real.rpow_nonneg (by linarith [(tripleTestBase_bounds T ht.1).2.1]) _
  obtain ⟨hS,hbound,_⟩ := tripleQuadrantN1_bounds ψ hψ hc
  have he := ha ω hω W T κ (tripleQuadrantN1 ψ) hW hw hT hκ hS ψ hbound hs
  rw [tripleQuadrant_residual_identity ω hω ψ hψ hc κ T hκ ht.1 hs,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq]
  apply (div_le_div_of_nonneg_right ((norm_integral_le_integral_norm _).trans he) hq.le).trans
  have hn := normalize_residual _ _ _ K _ hb hbq hL hK.le hp
    (ht.2.2.2.trans (mul_le_mul_of_nonneg_left hbq hK.le))
  have hw1 := fourierDerivativeL1_nonneg ω 1
  have hh := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ A*tripleQuadrantN1 ψ*(1+W+fourierDerivativeL1 ω 1) by positivity)
  dsimp only [K] at hh
  convert hh using 1 <;> ring

end
end HigherCorrelations
