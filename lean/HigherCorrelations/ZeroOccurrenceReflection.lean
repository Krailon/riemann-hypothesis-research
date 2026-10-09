import HigherCorrelations.ZeroOccurrences
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Multiplicity-preserving functional-equation reflection. UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

private theorem pos_re_ne_neg_nat {z : ℂ} (h : 0 < z.re) (n : ℕ) : z ≠ -n := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

private theorem zeta_order_le_one_sub (ρ : StripZero) :
    analyticOrderAt riemannZeta ρ.val ≤ analyticOrderAt riemannZeta (1 - ρ.val) := by
  let a : ℂ → ℂ := fun z => 2 * (2 * Real.pi : ℂ) ^ (-z) * Complex.Gamma z *
    Complex.cos (Real.pi * z / 2)
  have ha : AnalyticAt ℂ a ρ.val := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds ρ.property.2.1] with z hz
    have hg := Complex.differentiableAt_Gamma z (pos_re_ne_neg_nat hz)
    have hp : DifferentiableAt ℂ (fun z : ℂ => (2 * Real.pi : ℂ) ^ (-z)) z :=
      differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))))
    exact (((differentiableAt_const 2).mul hp).mul hg).mul (by fun_prop)
  have heq : (riemannZeta ∘ (fun z : ℂ => 1 - z)) =ᶠ[𝓝 ρ.val] a * riemannZeta := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds ρ.property.2.1,
      isOpen_lt Complex.continuous_re continuous_const |>.mem_nhds ρ.property.2.2] with z hz hz'
    exact riemannZeta_one_sub (pos_re_ne_neg_nat hz) (by
      intro he; simp [he] at hz')
  have hc : analyticOrderAt (riemannZeta ∘ (fun z : ℂ => 1 - z)) ρ.val =
      analyticOrderAt riemannZeta (1 - ρ.val) :=
    analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)
  rw [← hc, analyticOrderAt_congr heq, analyticOrderAt_mul ha (stripZero_analytic ρ)]
  exact le_add_left le_rfl

theorem zeroMultiplicity_one_sub (ρ : StripZero) :
    zeroMultiplicity (stripZeroOneSub ρ) = zeroMultiplicity ρ := by
  have h₁ := zeta_order_le_one_sub ρ
  have h₂ := zeta_order_le_one_sub (stripZeroOneSub ρ)
  have he : analyticOrderAt riemannZeta (1 - ρ.val) = analyticOrderAt riemannZeta ρ.val := by
    apply le_antisymm _ h₁
    simpa [stripZeroOneSub] using h₂
  exact congrArg ENat.toNat he

theorem zeroMultiplicity_horizontalReflection (ρ : StripZero) :
    zeroMultiplicity (stripZeroHorizontalReflection ρ) = zeroMultiplicity ρ := by
  rw [stripZeroHorizontalReflection, zeroMultiplicity_one_sub, zeroMultiplicity_conjugate]

private theorem occurrenceReflection_def (i : ZeroOccurrence) :
    occurrenceReflection i = ⟨stripZeroHorizontalReflection i.1,
      Fin.cast (zeroMultiplicity_horizontalReflection i.1).symm i.2⟩ := by
  rw [occurrenceReflection, dite_eq_left (zeroMultiplicity_horizontalReflection i.1)]

theorem occurrenceReflection_value (i : ZeroOccurrence) :
    occurrenceValue (occurrenceReflection i) = horizontalReflection (occurrenceValue i) := by
  simp only [occurrenceReflection, dite_eq_left (zeroMultiplicity_horizontalReflection i.1)]
  rfl

theorem occurrenceReflection_involutive : Function.Involutive occurrenceReflection := by
  intro i
  simp only [occurrenceReflection_def]
  apply Sigma.ext
  · apply Subtype.ext
    exact horizontalReflection_involutive i.1.val
  · apply (Fin.heq_ext_iff ((zeroMultiplicity_horizontalReflection _).trans
      (zeroMultiplicity_horizontalReflection _))).mpr
    rfl

theorem occurrenceReflection_ordinate (i : ZeroOccurrence) :
    occurrenceOrdinate (occurrenceReflection i) = occurrenceOrdinate i := by
  change (occurrenceValue (occurrenceReflection i)).im = _
  rw [occurrenceReflection_value]
  exact horizontalReflection_im _

theorem occurrenceReflection_displacement (i : ZeroOccurrence) :
    occurrenceDisplacement (occurrenceReflection i) = -occurrenceDisplacement i := by
  change (occurrenceValue (occurrenceReflection i)).re - 1 / 2 = _
  rw [occurrenceReflection_value]
  exact horizontalReflection_displacement _

end
end HigherCorrelations
