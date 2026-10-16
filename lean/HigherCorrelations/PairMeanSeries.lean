import HigherCorrelations.PairMeanDefinitions
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! UNCONDITIONAL absolute convergence of the frequency series and ordered
pair majorants. No separation bound on frequencies is used in this module. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem pairMeanCharacter_norm (u : ℝ) : ‖pairMeanCharacter u‖ = 1 := by
  simp [pairMeanCharacter, Complex.norm_exp]

theorem pairMeanCharacter_continuous : Continuous pairMeanCharacter := by
  unfold pairMeanCharacter
  fun_prop

theorem pairMeanCharacter_add (u v : ℝ) :
    pairMeanCharacter (u+v) = pairMeanCharacter u * pairMeanCharacter v := by
  simp only [pairMeanCharacter, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem pairMeanCharacter_conj (u : ℝ) :
    starRingEnd ℂ (pairMeanCharacter u) = pairMeanCharacter (-u) := by
  simp only [pairMeanCharacter, ← Complex.exp_conj, map_mul, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

theorem pairFrequency_product_summable {ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) :
    Summable (fun p : ι × ι => ‖c p.1‖*‖c p.2‖) :=
  hc.mul_of_nonneg hc (fun i => norm_nonneg _) (fun i => norm_nonneg _)

theorem pairFrequency_diagonal_summable {ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) : Summable (fun i => ‖c i‖^2) := by
  have h := (pairFrequency_product_summable c hc).comp_injective
    (show Function.Injective (fun i : ι => (i,i)) from fun i j he => congrArg Prod.fst he)
  simpa [Function.comp_def, pow_two] using h

theorem pairFrequency_nearby_summable {ι : Type*} (μ : ι → ℝ) (c : ι → ℂ)
    (δ : ℝ) (hc : Summable (fun i => ‖c i‖)) :
    Summable (fun p : ι × ι => if 0 < |μ p.1-μ p.2| ∧ |μ p.1-μ p.2| < δ
      then ‖c p.1‖*‖c p.2‖ else 0) := by
  apply Summable.of_nonneg_of_le _ _ (pairFrequency_product_summable c hc)
  · intro p
    split_ifs <;> positivity
  · intro p
    split_ifs
    · exact le_rfl
    · positivity

theorem pairFrequency_terms_summable {ι : Type*} (μ : ι → ℝ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (t : ℝ) :
    Summable (fun i => ‖c i*pairMeanCharacter (μ i*t)‖) := by
  simpa only [norm_mul, pairMeanCharacter_norm, mul_one] using hc

theorem pairFrequencySum_bound {ι : Type*} (μ : ι → ℝ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (t : ℝ) :
    ‖pairFrequencySum μ c t‖ ≤ ∑' i, ‖c i‖ := by
  have h := norm_tsum_le_tsum_norm (pairFrequency_terms_summable μ c hc t)
  simpa only [pairFrequencySum, norm_mul, pairMeanCharacter_norm, mul_one] using h

theorem pairFrequencySum_continuous {ι : Type*} (μ : ι → ℝ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) : Continuous (pairFrequencySum μ c) := by
  apply continuous_tsum (u := fun i => ‖c i‖)
  · intro i
    exact continuous_const.mul (pairMeanCharacter_continuous.comp (by fun_prop))
  · exact hc
  · intro i t
    simp [norm_mul, pairMeanCharacter_norm]

theorem pairFrequencySum_sq_integrableOn {ι : Type*} (μ : ι → ℝ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (T : ℝ) :
    IntegrableOn (fun t => ‖pairFrequencySum μ c t‖^2) (Set.Icc 0 T) :=
  ((pairFrequencySum_continuous μ c hc).norm.pow 2).continuousOn.integrableOn_Icc

end
end HigherCorrelations
