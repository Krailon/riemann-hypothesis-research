import HigherCorrelations.ScalarKernel
import Mathlib.LinearAlgebra.Lagrange
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-! UNCONDITIONAL finite partial fractions and real-line truncations.
Only the elementary finite-interval integration lemma is imported from the
rectangle file. No residue scaffold is used. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory
open scoped Topology

theorem simple_pole_partial_fractions {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ℂ) (hp : Function.Injective p) (z : ℂ) (hz : ∀ i, z ≠ p i) :
    (∏ i, (z-p i))⁻¹ = ∑ i, (∏ j ∈ Finset.univ.erase i, (p i-p j))⁻¹ / (z-p i) := by
  have h := congrArg (Polynomial.eval z) (Lagrange.sum_basis (s := Finset.univ)
    (v := p) (fun i _ j _ hij => hp hij) Finset.univ_nonempty)
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_one, Lagrange.basis,
    Polynomial.eval_prod, Lagrange.basisDivisor, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib] at h
  have hn : (∏ i, (z-p i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hz i))
  rw [inv_eq_one_div]
  symm
  apply (eq_div_iff hn).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ i, (∏ j ∈ Finset.univ.erase i, (p i-p j))⁻¹ *
        ∏ j ∈ Finset.univ.erase i, (z-p j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      rw [div_eq_mul_inv]
      calc
        _ = (∏ j ∈ Finset.univ.erase i, (p i-p j))⁻¹ *
            ((z-p i)⁻¹ * (z-p i)) * (∏ j ∈ Finset.univ.erase i, (z-p j)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (sub_ne_zero.mpr (hz i))]; ring
    _ = 1 := h

theorem simple_pole_interval (p : ℂ) (hp : p.im ≠ 0) (u v : ℝ) :
    (∫ x : ℝ in u..v, ((x : ℂ)-p)⁻¹) =
      ((Real.log ((v-p.re)^2+p.im^2) / 2 - Real.log ((u-p.re)^2+p.im^2) / 2 : ℝ) : ℂ) +
      Complex.I * (Real.arctan ((v-p.re)/p.im) - Real.arctan ((u-p.re)/p.im)) := by
  have he : (fun x : ℝ => ((x : ℂ)-p)⁻¹) =
      fun x : ℝ => (1 : ℂ) / ((x-p.re : ℝ) + (-p.im) * Complex.I) := by
    funext x
    rw [one_div]
    congr 1
    apply Complex.ext <;> simp
  rw [he, intervalIntegral.integral_comp_sub_right
    (fun x : ℝ => (1 : ℂ) / ((x : ℂ) + (-p.im) * Complex.I)) p.re]
  have h := integral_const_div_self_add_im (A := (1 : ℂ))
    (x₁ := u-p.re) (x₂ := v-p.re) (neg_ne_zero.mpr hp)
  convert h using 1 <;> simp [div_neg, Real.arctan_neg]; ring

end
end HigherCorrelations
