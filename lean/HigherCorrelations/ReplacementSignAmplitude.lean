import HigherCorrelations.ReplacementExponential
import HigherCorrelations.SignedSectorGeometry

/-! UNCONDITIONAL finite exponential remainder representation, with sharp hexagonal growth. -/
namespace HigherCorrelations
noncomputable section

theorem replacementLinear_apply (θ : Fin 3 → ℝ) (e : Fin 3 → Bool) (p : ℝ × ℝ) :
    replacementLinear θ e p = ((replacementSigned θ e 0*(p.1+p.2)+
      replacementSigned θ e 1*p.1+replacementSigned θ e 2*p.2:ℝ):ℂ) := by
  simp only [replacementLinear, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  ring

private theorem signed_abs (θ : Fin 3 → ℝ) (e : Fin 3 → Bool) (j : Fin 3) :
    |replacementSigned θ e j|=|θ j| := by simp [replacementSigned, apply_ite abs]

theorem replacementLinear_bounds (θ : Fin 3 → ℝ) (e : Fin 3 → Bool) (x s : ℝ)
    (hx : 0 ≤ x) (hs : s ≤ 1) (hθ : ∀ j, |θ j| ≤ x) (p : ℝ × ℝ)
    (hp : signedGauge p ≤ s) :
    ‖replacementLinear θ e p‖ ≤ 2*s*x ∧ ‖replacementLinear θ e p‖ ≤ 2*x ∧
    ∀ j, ‖replacementLinear θ e (replacementCoordinate j)‖ ≤ 2*x := by
  have hb (p : ℝ × ℝ) : ‖replacementLinear θ e p‖  ≤  2*signedGauge p*x := by
    rw [replacementLinear_apply, Complex.norm_real, Real.norm_eq_abs]
    have hh := (abs_add_le (replacementSigned θ e 0*(p.1+p.2)+replacementSigned θ e 1*p.1)
      (replacementSigned θ e 2*p.2)).trans (add_le_add (abs_add_le _ _) le_rfl)
    simp only [abs_mul, signed_abs] at hh
    have h0 := mul_le_mul_of_nonneg_right (hθ 0) (abs_nonneg (p.1+p.2))
    have h1 := mul_le_mul_of_nonneg_right (hθ 1) (abs_nonneg p.1)
    have h2 := mul_le_mul_of_nonneg_right (hθ 2) (abs_nonneg p.2)
    rw [signedGauge_half_sum]
    nlinarith
  have h : ‖replacementLinear θ e p‖ ≤ 2*s*x := (hb p).trans (by gcongr)
  refine ⟨h, h.trans (by nlinarith), ?_⟩
  intro j
  have hh := hb (replacementCoordinate j)
  cases j <;> simpa [replacementCoordinate, signedGauge] using hh

theorem replacementLinear_sum_zero (θ : Fin 3 → ℝ) (p : ℝ × ℝ) :
    (∑ e : Fin 3 → Bool, replacementLinear θ e p)=0 := by
  have hn (e : Fin 3 → Bool) : replacementLinear θ (fun j => !(e j)) p = -replacementLinear θ e p := by
    simp only [replacementLinear_apply]
    have h (j) : replacementSigned θ (fun j => !(e j)) j = -replacementSigned θ e j := by
      simp [replacementSigned]; split <;> simp_all
    simp only [h]
    push_cast
    ring
  have he := Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin 3 => Equiv.boolNot))
    (fun e => replacementLinear θ (fun j => !(e j)) p) (fun e => replacementLinear θ e p)
    (fun _ => rfl)
  simp only [hn, Finset.sum_neg_distrib] at he
  linear_combination -(1/2:ℂ)*he

theorem replacementCosh_remainders (θ : Fin 3 → ℝ) (p : ℝ × ℝ) :
    replacementCosh 1 θ p = (1/8:ℂ)*∑ e : Fin 3 → Bool,
      replacementExpRemainder (replacementLinear θ e) p := by
  let c : Fin 3 → ℂ := ![(θ 0*(p.1+p.2):ℝ), (θ 1*p.1:ℝ), (θ 2*p.2:ℝ)]
  have he (e : Fin 3 → Bool) : (∑ j, if e j then -c j else c j) = replacementLinear θ e p := by
    rw [replacementLinear_apply]
    simp only [Fin.sum_univ_three, c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    simp [replacementSigned, apply_ite (fun x : ℝ => (x:ℂ)), ite_mul]
  have hp := Fintype.prod_sum (fun (j : Fin 3) (b : Bool) => Complex.exp (if b then -c j else c j))
  have hx : (∑ e : Fin 3 → Bool, Complex.exp (replacementLinear θ e p)) =
      (2*Complex.cosh (c 0))*(2*Complex.cosh (c 1))*(2*Complex.cosh (c 2)) := by
    simp_rw [← he, Complex.exp_sum]
    rw [← hp]
    simp [Fin.prod_univ_three, Complex.cosh, add_comm]
    <;> ring
  simp only [replacementExpRemainder, Finset.sum_sub_distrib, replacementLinear_sum_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.reducePow, nsmul_eq_mul, mul_one, sub_zero, hx]
  simp [replacementCosh, c]
  ring

end
end HigherCorrelations
