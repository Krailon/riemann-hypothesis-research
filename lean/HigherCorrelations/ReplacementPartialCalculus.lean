import HigherCorrelations.ConstantReplacementDefinitions
import HigherCorrelations.ComplexFourierDecay
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! UNCONDITIONAL coordinate derivatives and integration by parts in project units. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped ContDiff

theorem replacementPartial_smooth (j : Bool) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (replacementPartial j f) := by
  exact (hf.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)

theorem replacementDeriv_succ (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ) :
    replacementDeriv j (n+1) f = replacementPartial j (replacementDeriv j n f) := by
  exact Function.iterate_succ_apply' _ _ _

theorem replacementDeriv_succ_right (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ) :
    replacementDeriv j (n+1) f = replacementDeriv j n (replacementPartial j f) := by
  exact Function.iterate_succ_apply _ _ _

theorem replacementDeriv_smooth (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (replacementDeriv j n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [replacementDeriv_succ]; exact replacementPartial_smooth j _ ih

theorem replacementDeriv_support (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ) :
    tsupport (replacementDeriv j n f) ⊆ tsupport f := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    rw [replacementDeriv_succ]
    exact (tsupport_fderiv_apply_subset ℝ _).trans ih

theorem replacementDeriv_compact (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ)
    (hc : HasCompactSupport f) : HasCompactSupport (replacementDeriv j n f) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (replacementDeriv_support j n f)

theorem replacementDeriv_integrable (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Integrable (replacementDeriv j n f) :=
  (replacementDeriv_smooth j n f hf).continuous.integrable_of_hasCompactSupport
    (replacementDeriv_compact j n f hc)

private theorem partial_add (j : Bool) (f g : ℝ × ℝ → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    replacementPartial j (fun p => f p+g p) = fun p => replacementPartial j f p+replacementPartial j g p := by
  funext p
  unfold replacementPartial
  change fderiv ℝ (f+g) p (replacementCoordinate j) = _
  rw [((hf p).hasFDerivAt.add (hg p).hasFDerivAt).fderiv]
  rfl

theorem replacementDeriv_add (j : Bool) (n : ℕ) (f g : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    replacementDeriv j n (fun p => f p+g p) = fun p => replacementDeriv j n f p+replacementDeriv j n g p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replacementDeriv_succ, ih]
    exact partial_add j _ _ ((replacementDeriv_smooth j n f hf).differentiable (by simp))
      ((replacementDeriv_smooth j n g hg).differentiable (by simp))

private theorem partial_mul (j : Bool) (f g : ℝ × ℝ → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    replacementPartial j (fun p => f p*g p) = fun p =>
      replacementPartial j f p*g p+f p*replacementPartial j g p := by
  funext p
  unfold replacementPartial
  change fderiv ℝ (f*g) p (replacementCoordinate j) = _
  rw [((hf p).hasFDerivAt.mul (hg p).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem replacementDeriv_product_bound (j : Bool) (n : ℕ) (f g : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (p : ℝ × ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfb : ∀ k ≤ n, ‖replacementDeriv j k f p‖ ≤ A)
    (hgb : ∀ k ≤ n, ‖replacementDeriv j k g p‖ ≤ B) :
    ‖replacementDeriv j n (fun p => f p*g p) p‖  ≤  2^n*A*B := by
  induction n generalizing f g with
  | zero =>
    change ‖f p*g p‖  ≤  _
    rw [norm_mul]
    simpa [replacementDeriv] using mul_le_mul (hfb 0 le_rfl) (hgb 0 le_rfl) (norm_nonneg _) hA
  | succ n ih =>
    rw [replacementDeriv_succ_right, partial_mul j f g
      (hf.differentiable (by simp)) (hg.differentiable (by simp)),
      replacementDeriv_add j n _ _ ((replacementPartial_smooth j f hf).mul hg)
        (hf.mul (replacementPartial_smooth j g hg))]
    have h1 := ih (replacementPartial j f) g (replacementPartial_smooth j f hf) hg
      (fun k hk => by rw [← replacementDeriv_succ_right]; exact hfb (k+1) (by omega))
      (fun k hk => hgb k (by omega))
    have h2 := ih f (replacementPartial j g) hf (replacementPartial_smooth j g hg)
      (fun k hk => hfb k (by omega))
      (fun k hk => by rw [← replacementDeriv_succ_right]; exact hgb (k+1) (by omega))
    have h := norm_add_le (replacementDeriv j n (fun p => replacementPartial j f p*g p) p)
      (replacementDeriv j n (fun p => f p*replacementPartial j g p) p)
    simp only [pow_succ]
    linarith

theorem replacementP24_nonneg (φ : ℝ × ℝ → ℂ) : 0  ≤  replacementP24 φ := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact integral_nonneg (fun _ => norm_nonneg _)

theorem replacementP24_pure (φ : ℝ × ℝ → ℂ) (j : Bool) (n : ℕ) (hn : n ≤ 24) :
    (∫ p, ‖replacementDeriv j n φ p‖)  ≤  replacementP24 φ := by
  have hp (i k : ℕ) : 0  ≤  ∫ p, ‖replacementDeriv false i (replacementDeriv true k φ) p‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  unfold replacementP24
  have ho (i : ℕ) (hi : i<25) :
      (∑ k ∈ Finset.range (25-i), ∫ p, ‖replacementDeriv false i (replacementDeriv true k φ) p‖)  ≤
      ∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range (25-i),
        ∫ p, ‖replacementDeriv false i (replacementDeriv true k φ) p‖ :=
    Finset.single_le_sum (f := fun i => ∑ k ∈ Finset.range (25-i),
      ∫ p, ‖replacementDeriv false i (replacementDeriv true k φ) p‖)
      (fun i _ => Finset.sum_nonneg (fun k _ => hp i k)) (Finset.mem_range.mpr hi)
  cases j
  · apply le_trans _ (ho n (by omega))
    simpa only [replacementDeriv, Function.iterate_zero, id_eq] using
      (Finset.single_le_sum (f := fun k => ∫ p, ‖replacementDeriv false n (replacementDeriv true k φ) p‖)
        (fun k _ => hp n k) (show 0∈Finset.range (25-n) by simp; omega))
  · apply le_trans _ (ho 0 (by omega))
    simpa only [replacementDeriv, Function.iterate_zero, id_eq] using
      (Finset.single_le_sum (f := fun k => ∫ p, ‖replacementDeriv false 0 (replacementDeriv true k φ) p‖)
        (fun k _ => hp 0 k) (show n∈Finset.range (25-0) by simp; omega))

end
end HigherCorrelations
