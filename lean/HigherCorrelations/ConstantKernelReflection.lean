import HigherCorrelations.ConstantKernelDefinitions
import HigherCorrelations.ProfileTaylor
import HigherCorrelations.RationalKernelBounds

/-! UNCONDITIONAL eight-reflection average and horizontal quadratic bound. -/
namespace HigherCorrelations
noncomputable section

theorem constantKernelEmpty_profile (a d : ℝ) (δ : Fin 3 → ℝ) :
    constantKernelEmpty a d δ = (1/8:ℂ)*∑ e : Fin 3 → Bool,
      rationalProfile a d (if e 1 then -δ 1 else δ 1)
        (if e 2 then -δ 2 else δ 2) (if e 0 then -δ 0 else δ 0) := by
  simp [constantKernelEmpty, signCoefficient, signCharacter, horizontalProfile,
    constantKernelParameters]

private theorem parameters_bound (δ : Fin 3 → ℝ) (e : Fin 3 → Bool)
    (hδ : ∀ j, |δ j| ≤ 1/2) : ∀ j, |constantKernelParameters δ e j| ≤ 1/2 := by
  intro j
  fin_cases j
  · simpa [constantKernelParameters, apply_ite abs] using hδ 1
  · simpa [constantKernelParameters, apply_ite abs] using hδ 2
  · simpa [constantKernelParameters, apply_ite abs] using hδ 0

private theorem parameters_size (δ : Fin 3 → ℝ) (e : Fin 3 → Bool) :
    horizontalSize (constantKernelParameters δ e) = ∑ j, |δ j| := by
  simp [horizontalSize, constantKernelParameters, Fin.sum_univ_three, apply_ite abs]
  ring

private theorem average_bound (K : (Fin 3 → Bool) → ℂ) (B : ℝ)
    (hK : ∀ e, ‖K e‖ ≤ B) : ‖(1/8:ℂ)*∑ e, K e‖ ≤ B := by
  rw [norm_mul]
  norm_num
  have h := (norm_sum_le Finset.univ K).trans (Finset.sum_le_sum (fun e _ => hK e))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.reducePow, nsmul_eq_mul] at h
  norm_num at h
  linarith

private theorem neg_sum (K : (Fin 3 → Bool) → ℂ) :
    (∑ e : Fin 3 → Bool, K (fun j => !(e j))) = ∑ e, K e := by
  exact Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin 3 => Equiv.boolNot)) _ _
    (fun _ => rfl)

theorem constantKernelEmpty_symmetric (a d : ℝ) (δ : Fin 3 → ℝ) :
    constantKernelEmpty a d δ = (1/8:ℂ)*∑ e : Fin 3 → Bool,
      (horizontalProfile a d (constantKernelParameters δ e)+
        horizontalProfile a d (-constantKernelParameters δ e))/2 := by
  have hn (e : Fin 3 → Bool) :
      constantKernelParameters δ (fun j => !(e j)) = -constantKernelParameters δ e := by
    funext j
    fin_cases j <;> simp [constantKernelParameters] <;> split <;> simp_all
  have hs := neg_sum (fun e => horizontalProfile a d (constantKernelParameters δ e))
  simp only [hn] at hs
  simp only [constantKernelEmpty, signCoefficient, signCharacter, Finset.prod_empty,
    one_mul]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hs]
  ring

theorem constantKernelEmpty_horizontal_bound (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖constantKernelEmpty a d δ-rationalProfile a d 0 0 0‖ ≤
      3072*Real.pi*(∑ j, δ j^2) := by
  have hs : (∑ j, |δ j|)^2 ≤ 3*(∑ j, δ j^2) := by
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (|δ 0|-|δ 1|), sq_nonneg (|δ 0|-|δ 2|),
      sq_nonneg (|δ 1|-|δ 2|), sq_abs (δ 0), sq_abs (δ 1), sq_abs (δ 2)]
  have hb (e : Fin 3 → Bool) :=
    profile_symmetric_second_bound a d (constantKernelParameters δ e) (parameters_bound δ e hδ)
  have hb' (e : Fin 3 → Bool) :
      ‖(horizontalProfile a d (constantKernelParameters δ e)+
          horizontalProfile a d (-constantKernelParameters δ e))/2-
        horizontalProfile a d 0‖ ≤ 3072*Real.pi*(∑ j, δ j^2) := by
    have hh := hb e
    rw [parameters_size] at hh
    norm_num [profileDerivativeBound] at hh
    have hp := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
    nlinarith
  have ha := average_bound _ _ hb'
  rw [Finset.sum_sub_distrib, mul_sub, ← constantKernelEmpty_symmetric] at ha
  simpa [horizontalProfile] using ha

theorem constantKernelEmpty_global_bound (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) : ‖constantKernelEmpty a d δ‖ ≤ 7*Real.pi/9 := by
  change ‖signCoefficient _ ∅‖ ≤ _
  simp only [signCoefficient, signCharacter, Finset.prod_empty, one_mul]
  apply average_bound
  intro e
  exact rationalProfile_bound a d _ _ _ (parameters_bound δ e hδ 0)
    (parameters_bound δ e hδ 1) (parameters_bound δ e hδ 2)

end
end HigherCorrelations
