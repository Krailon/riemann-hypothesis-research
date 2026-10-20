import HigherCorrelations.PairKernelIntegral
import HigherCorrelations.PairZeroVectors
import HigherCorrelations.Zeta23Counting
import HigherCorrelations.ZeroOccurrenceReflection
import Mathlib.MeasureTheory.Group.Integral

/-! UNCONDITIONAL finite squared norm, with all occurrence pairs and horizontal
reflection. Every termwise integral below is a finite integrable sum. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

theorem pairZeroVector_product (i j : ZeroOccurrence) (X t : ℝ) :
    pairZeroVector i X t * star (pairZeroVector j X t) =
      Complex.exp ((Real.log X : ℂ)*(occurrenceValue i+star (occurrenceValue j)-1)) *
        pairKernelProduct (occurrenceOrdinate i-occurrenceOrdinate j)
          (occurrenceDisplacement i) (-occurrenceDisplacement j) (t-occurrenceOrdinate j) := by
  have hk (x e : ℝ) : star (scalarKernel x e) = scalarKernel x (-e) := by
    change conj (scalarKernel x e) = scalarKernel x (-e)
    simp only [scalarKernel,map_inv₀,map_add,map_one,map_pow,map_mul,
      Complex.conj_ofReal,Complex.conj_I]
    push_cast
    congr 3
    ring
  have he : (occurrenceDisplacement i : ℂ)+Complex.I*occurrenceOrdinate i +
      conj ((occurrenceDisplacement j : ℂ)+Complex.I*occurrenceOrdinate j) =
      occurrenceValue i+star (occurrenceValue j)-1 := by
    apply Complex.ext <;> simp [occurrenceDisplacement,occurrenceOrdinate] <;> ring
  have hexp : Complex.exp ((Real.log X : ℂ)*
      ((occurrenceDisplacement i : ℂ)+Complex.I*occurrenceOrdinate i)) *
      star (Complex.exp ((Real.log X : ℂ)*
        ((occurrenceDisplacement j : ℂ)+Complex.I*occurrenceOrdinate j))) =
      Complex.exp ((Real.log X : ℂ)*(occurrenceValue i+star (occurrenceValue j)-1)) := by
    simp only [Complex.star_def,← Complex.exp_conj,← Complex.exp_add,map_mul,Complex.conj_ofReal]
    rw [← mul_add,he]
    rfl
  unfold pairZeroVector
  rw [star_mul,hk]
  calc
    _ = (Complex.exp ((Real.log X : ℂ)*(occurrenceDisplacement i+Complex.I*occurrenceOrdinate i)) *
        star (Complex.exp ((Real.log X : ℂ)*(occurrenceDisplacement j+Complex.I*occurrenceOrdinate j)))) *
        (scalarKernel (t-occurrenceOrdinate i) (occurrenceDisplacement i) *
        scalarKernel (t-occurrenceOrdinate j) (-occurrenceDisplacement j)) := by ring
    _ = _ := by
      rw [hexp]
      congr 1
      unfold pairKernelProduct
      congr 2
      ring

theorem pairZeroVector_product_integrable (i j : ZeroOccurrence) (X : ℝ) :
    Integrable (fun t => pairZeroVector i X t * star (pairZeroVector j X t)) := by
  have hi : |occurrenceDisplacement i| ≤ 3/4 := by linarith [pair_occurrence_displacement i]
  have hj : |-occurrenceDisplacement j| ≤ 3/4 := by rw [abs_neg]; linarith [pair_occurrence_displacement j]
  have h := (pairKernelProduct_integrable (occurrenceOrdinate i-occurrenceOrdinate j)
    (occurrenceDisplacement i) (-occurrenceDisplacement j) hi hj).comp_sub_right (occurrenceOrdinate j)
  simpa only [pairZeroVector_product] using h.const_mul
    (Complex.exp ((Real.log X : ℂ)*(occurrenceValue i+star (occurrenceValue j)-1)))

theorem pairZeroVector_product_integral (i j : ZeroOccurrence) (X : ℝ) :
    (∫ t : ℝ, pairZeroVector i X t * star (pairZeroVector j X t)) =
      Complex.exp ((Real.log X : ℂ)*(occurrenceValue i+star (occurrenceValue j)-1)) *
        (2*Real.pi/(4-(occurrenceValue i+star (occurrenceValue j)-1)^2)) := by
  simp_rw [pairZeroVector_product]
  rw [integral_const_mul,integral_sub_right_eq_self]
  change _ * pairKernelIntegral _ _ _ = _
  rw [pairKernelIntegral_eq _ _ _ (by linarith [pair_occurrence_displacement i])
    (by rw [abs_neg]; linarith [pair_occurrence_displacement j])]
  congr 1
  unfold pairKernelValue
  congr 1
  have he : ((occurrenceOrdinate i-occurrenceOrdinate j : ℝ):ℂ)+
      Complex.I*((-occurrenceDisplacement j)-occurrenceDisplacement i) =
      -Complex.I*(occurrenceValue i+star (occurrenceValue j)-1) := by
    apply Complex.ext <;> simp [occurrenceDisplacement,occurrenceOrdinate] <;> ring
  simp only [Complex.ofReal_neg]
  rw [he]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem pairZero_finite_square (s : Finset ZeroOccurrence) (X t : ℝ) :
    ((‖∑ i ∈ s, pairZeroVector i X t‖^2 : ℝ):ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, pairZeroVector i X t * star (pairZeroVector j X t) := by
  rw [← Finset.sum_mul_sum]
  simp only [← star_sum]
  simpa only [Complex.ofReal_pow,Complex.star_def] using (Complex.mul_conj' _).symm

theorem pairZeroWindow_square_integrable (X T : ℝ) :
    Integrable (fun t => ‖pairZeroWindowVector X T t‖^2) := by
  have h : Integrable (fun t => ∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
      pairZeroVector i X t * star (pairZeroVector j X t)) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      pairZeroVector_product_integrable i j X))
  have he (t : ℝ) : (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
      pairZeroVector i X t * star (pairZeroVector j X t)).re = ‖pairZeroWindowVector X T t‖^2 := by
    rw [← pairZero_finite_square]; rfl
  have hh : Integrable (fun t => (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
      pairZeroVector i X t * star (pairZeroVector j X t)).re) := h.re
  simpa only [he] using hh

theorem pairZeroWindow_reflection (T : ℝ) (i : ZeroOccurrence) :
    occurrenceReflection i ∈ occurrenceWindow 0 T ↔ i ∈ occurrenceWindow 0 T := by
  simp only [mem_occurrenceWindow,occurrenceReflection_ordinate]

theorem pairCorrelationSum_norm (X T : ℝ) (_hX : 0 < X) :
    pairCorrelationSum X T = ((2/Real.pi * ∫ t : ℝ, ‖pairZeroWindowVector X T t‖^2 : ℝ):ℂ) := by
  classical
  have hs : (∫ t : ℝ, ((‖pairZeroWindowVector X T t‖^2 : ℝ):ℂ)) =
      ∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
        Complex.exp ((Real.log X : ℂ)*(occurrenceValue i+star (occurrenceValue j)-1)) *
          (2*Real.pi/(4-(occurrenceValue i+star (occurrenceValue j)-1)^2)) := by
    simp_rw [pairZeroWindowVector,pairZero_finite_square]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      pairZeroVector_product_integrable i j X))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (fun j _ => pairZeroVector_product_integrable i j X)]
    simp_rw [pairZeroVector_product_integral]
  rw [integral_complex_ofReal] at hs
  have hr (i : ZeroOccurrence) :
      (∑ j ∈ occurrenceWindow 0 T,
        Complex.exp ((Real.log X : ℂ)*(occurrenceValue i+star (occurrenceValue j)-1)) *
          (2*Real.pi/(4-(occurrenceValue i+star (occurrenceValue j)-1)^2))) =
      ∑ j ∈ occurrenceWindow 0 T,
        Complex.exp ((Real.log X : ℂ)*(occurrenceValue i-occurrenceValue j)) *
          (2*Real.pi/(4-(occurrenceValue i-occurrenceValue j)^2)) := by
    apply Finset.sum_bij (fun j _ => occurrenceReflection j)
    · intro j hj; exact (pairZeroWindow_reflection T j).mpr hj
    · intro j hj k hk h; exact occurrenceReflection_involutive.injective h
    · intro j hj
      exact ⟨occurrenceReflection j,(pairZeroWindow_reflection T j).mpr hj,
        occurrenceReflection_involutive j⟩
    · intro j hj
      rw [occurrenceReflection_value]
      unfold horizontalReflection
      simp only [Complex.star_def]
      congr 2 <;> ring
  simp_rw [hr] at hs
  push_cast
  rw [hs]
  unfold pairCorrelationSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  field_simp
  <;> ring

theorem pairCorrelationSum_im (X T : ℝ) (hX : 0 < X) : (pairCorrelationSum X T).im = 0 := by
  rw [pairCorrelationSum_norm X T hX]
  rfl

theorem pairCorrelationSum_re_nonneg (X T : ℝ) (hX : 0 < X) :
    0 ≤ (pairCorrelationSum X T).re := by
  rw [pairCorrelationSum_norm X T hX]
  simp only [Complex.ofReal_re]
  exact mul_nonneg (by positivity) (integral_nonneg (fun t => sq_nonneg _))

end
end HigherCorrelations
