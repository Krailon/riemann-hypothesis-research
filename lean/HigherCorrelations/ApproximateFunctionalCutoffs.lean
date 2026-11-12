import HigherCorrelations.ApproximateFunctionalAlgebra
import HigherCorrelations.ApproximateFunctionalPhase
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor

/-! UNCONDITIONAL inclusive-cutoff identities, elementary polynomial bounds,
and the actual asymmetric scales used by the twisted second moment. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Set

theorem afePolynomial_norm_le_sum (s : ℂ) (x : ℝ) :
    ‖afePolynomial s x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)^(-s.re) := by
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro n hn
  simpa using norm_natCast_cpow_of_pos (Finset.mem_Icc.mp hn).1 (-s)

theorem afePolynomial_norm_le_floor (s : ℂ) (hs : 0 ≤ s.re) (x : ℝ) :
    ‖afePolynomial s x‖ ≤ ⌊x⌋₊ := by
  apply (afePolynomial_norm_le_sum s x).trans
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (Finset.mem_Icc.mp hn).1
      · linarith
    _ = _ := by simp

theorem afePolynomial_norm_le (s : ℂ) (hs : 0 ≤ s.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖afePolynomial s x‖ ≤ x :=
  (afePolynomial_norm_le_floor s hs x).trans (Nat.floor_le hx)

theorem afePolynomial_step (s : ℂ) (N : ℕ) :
    afePolynomial s (N+1 : ℕ) = afePolynomial s N + (N+1 : ℂ)^(-s) := by
  simp only [afePolynomial_nat]
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast; rfl

theorem afeTwist_admissible (μ₁ μ₂ T t : ℝ)
    (hμ : 1 ≤ μ₁) (horder : μ₁ ≤ μ₂) (hmax : μ₂ ≤ T/(2*Real.pi))
    (ht : T ≤ t) :
    1 ≤ afeTwistShort μ₁ μ₂ t ∧
    afeTwistShort μ₁ μ₂ t ≤ afeTwistLong μ₁ μ₂ t ∧
    2*Real.pi * afeTwistShort μ₁ μ₂ t * afeTwistLong μ₁ μ₂ t = t := by
  have hp : 0 < 2*Real.pi := by positivity
  have h₁ : 0 < μ₁ := by linarith
  have h₂ : 0 < μ₂ := lt_of_lt_of_le h₁ horder
  have hT : 2*Real.pi*μ₂ ≤ T := by
    have := (le_div_iff₀ hp).mp hmax
    nlinarith
  have htpos : 0 < t := lt_of_lt_of_le (mul_pos hp h₂) (hT.trans ht)
  have hshort : 1 ≤ t*μ₁/(2*Real.pi*μ₂) := by
    apply (le_div_iff₀ (mul_pos hp h₂)).mpr
    nlinarith
  have hord : t*μ₁/(2*Real.pi*μ₂) ≤ t*μ₂/(2*Real.pi*μ₁) := by
    apply (div_le_div_iff₀ (mul_pos hp h₂) (mul_pos hp h₁)).mpr
    have := mul_self_le_mul_self h₁.le horder
    have := mul_le_mul_of_nonneg_left this (le_of_lt (mul_pos htpos hp))
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hshort)
  · exact Real.sqrt_le_sqrt hord
  · unfold afeTwistShort afeTwistLong
    have he : (t*μ₁/(2*Real.pi*μ₂)) * (t*μ₂/(2*Real.pi*μ₁)) =
        (t/(2*Real.pi))^2 := by field_simp
    rw [mul_assoc, ← Real.sqrt_mul (by positivity), he, Real.sqrt_sq (by positivity)]
    field_simp

theorem afeTwist_short_continuous (μ₁ μ₂ : ℝ) : Continuous (afeTwistShort μ₁ μ₂) := by
  unfold afeTwistShort
  fun_prop

theorem afeTwist_long_continuous (μ₁ μ₂ : ℝ) : Continuous (afeTwistLong μ₁ μ₂) := by
  unfold afeTwistLong
  fun_prop

theorem afePolynomial_continuous (x : ℝ) : Continuous (fun s : ℂ => afePolynomial s x) := by
  unfold afePolynomial
  apply continuous_finset_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  letI : NeZero (n : ℂ) := ⟨hn0⟩
  exact (continuous_const_cpow (n : ℂ)).comp continuous_neg

theorem afePolynomial_measurable {s : ℝ → ℂ} {x : ℝ → ℝ}
    (hs : Measurable s) (hx : Measurable x) :
    Measurable (fun t => afePolynomial (s t) (x t)) := by
  have h : Measurable (fun p : ℂ × ℕ => afePolynomial p.1 p.2) :=
    measurable_from_prod_countable_left (fun N => (afePolynomial_continuous N).measurable)
  convert h.comp (hs.prodMk hx.nat_floor) using 1
  ext t
  simp [afePolynomial]

theorem afePolynomial_integrableOn {s : ℝ → ℂ} {x : ℝ → ℝ} (a b B : ℝ)
    (hs : Measurable s) (hx : Measurable x)
    (hσ : ∀ t ∈ Icc a b, 0 ≤ (s t).re)
    (hbound : ∀ t ∈ Icc a b, 0 ≤ x t ∧ x t ≤ B) :
    IntegrableOn (fun t => afePolynomial (s t) (x t)) (Icc a b) := by
  apply Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    (afePolynomial_measurable hs hx).aestronglyMeasurable (M := B)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (afePolynomial_norm_le (s t) (hσ t ht) (hbound t ht).1).trans (hbound t ht).2

theorem afePolynomial_continuousCutoff_integrable (σ ε a b : ℝ) (hσ : 0 ≤ σ)
    (x : ℝ → ℝ) (hx : Continuous x) (hx₀ : ∀ t, 0 ≤ x t) :
    IntegrableOn (fun t => afePolynomial (afePoint σ (ε*t)) (x t)) (Icc a b) := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hx.continuousOn
  apply afePolynomial_integrableOn a b B
    (by unfold afePoint; fun_prop) hx.measurable
    (fun t _ => by simpa [afePoint] using hσ)
  intro t ht
  refine ⟨hx₀ t, ?_⟩
  exact (le_abs_self (x t)).trans (by simpa [Real.norm_eq_abs] using hB t ht)

theorem afeTwist_four_polynomials_integrable (σ μ₁ μ₂ a b : ℝ)
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) :
    IntegrableOn (fun t => afePolynomial (afePoint σ t) (afeTwistShort μ₁ μ₂ t)) (Icc a b) ∧
    IntegrableOn (fun t => afePolynomial (1-afePoint σ t) (afeTwistLong μ₁ μ₂ t)) (Icc a b) ∧
    IntegrableOn (fun t => afePolynomial (afePoint σ (-t)) (afeTwistLong μ₁ μ₂ t)) (Icc a b) ∧
    IntegrableOn (fun t => afePolynomial (1-afePoint σ (-t)) (afeTwistShort μ₁ μ₂ t)) (Icc a b) := by
  have hshort := afeTwist_short_continuous μ₁ μ₂
  have hlong := afeTwist_long_continuous μ₁ μ₂
  have hshort₀ (t : ℝ) : 0 ≤ afeTwistShort μ₁ μ₂ t := Real.sqrt_nonneg _
  have hlong₀ (t : ℝ) : 0 ≤ afeTwistLong μ₁ μ₂ t := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using afePolynomial_continuousCutoff_integrable σ 1 a b hσ _ hshort hshort₀
  · simpa [afePoint_reflect] using
      afePolynomial_continuousCutoff_integrable (1-σ) (-1) a b (by linarith) _ hlong hlong₀
  · simpa using afePolynomial_continuousCutoff_integrable σ (-1) a b hσ _ hlong hlong₀
  · simpa [afePoint_reflect] using
      afePolynomial_continuousCutoff_integrable (1-σ) 1 a b (by linarith) _ hshort hshort₀

end
end HigherCorrelations
