import HigherCorrelations.ReplacementSignAmplitude
import HigherCorrelations.ReplacementFourierDecay

/-! UNCONDITIONAL uniform quadratic complex-test decay with the exact P24 seminorm. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped ContDiff

theorem replacementAmplitude_L1 (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (θ : Fin 3 → ℝ) (e : Fin 3 → Bool)
    (x s : ℝ) (hx : 0 ≤ x) (hs : s ≤ 1) (hθ : ∀ j, |θ j| ≤ x)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (j : Bool) (n : ℕ) (hn : n ≤ 22) :
    (∫ p, ‖replacementDeriv j n (fun p => φ p*replacementExpRemainder (replacementLinear θ e) p) p‖)  ≤
      2^22*23*replacementP24 φ*(2^24*x^2*(1+x)^22*Real.exp (2*s*x)) := by
  let g := replacementExpRemainder (replacementLinear θ e)
  let B := (2:ℝ)^24*x^2*(1+x)^22*Real.exp (2*s*x)
  let A := fun p => ∑ k ∈ Finset.range 23, ‖replacementDeriv j k φ p‖
  have hg : ContDiff ℝ ∞ g := replacementExpRemainder_smooth _
  have hA (p) : 0 ≤ A p := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hiA : Integrable A := integrable_finset_sum _ (fun k _ => (replacementDeriv_integrable j k φ hφ hc).norm)
  have hprod : HasCompactSupport (fun p => φ p*g p) := hc.mul_right
  have hb (p) : ‖replacementDeriv j n (fun p => φ p*g p) p‖  ≤  2^22*A p*B := by
    by_cases hp : p∈tsupport φ
    · have hlin := replacementLinear_bounds θ e x s hx hs hθ p (hsupp p hp)
      have hh := replacementDeriv_product_bound j n φ g hφ hg p (A p) B (hA p) hB
        (fun k hk => Finset.single_le_sum (f := fun k => ‖replacementDeriv j k φ p‖) (fun k _ => norm_nonneg _) (show k∈Finset.range 23 by simp; omega))
        (fun k hk => replacementExpRemainder_jet_bound j _ p x (2*s*x) hx hlin.2.1 hlin.1 (hlin.2.2 j) k (by omega))
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn) (hA p)) hB)
    · have hz : replacementDeriv j n (fun p => φ p*g p) p=0 := by
        by_contra hn
        exact hp (tsupport_mul_subset_left (replacementDeriv_support j n _ (subset_tsupport _ hn)))
      rw [hz, norm_zero]
      positivity
  have hint := integral_mono (replacementDeriv_integrable j n _ (hφ.mul hg) hprod).norm
    ((hiA.const_mul _).mul_const _) hb
  have hAint : (∫ p, A p)  ≤  23*replacementP24 φ := by
    rw [integral_finset_sum _ (fun k _ => (replacementDeriv_integrable j k φ hφ hc).norm)]
    calc
      _  ≤  ∑ k ∈ Finset.range 23, replacementP24 φ := Finset.sum_le_sum (fun k hk => replacementP24_pure φ j k (by simp only [Finset.mem_range] at hk; omega))
      _ = _ := by simp
  rw [integral_mul_const, integral_const_mul] at hint
  apply hint.trans
  calc
    _ ≤ (2^22*(23*replacementP24 φ))*B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAint (by positivity)) hB
    _ = _ := by dsimp [B]; ring

theorem replacementRemainder_fourier_bound (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (θ : Fin 3 → ℝ) (e : Fin 3 → Bool)
    (x s : ℝ) (hx : 0 ≤ x) (hs : s ≤ 1) (hθ : ∀ j, |θ j| ≤ x)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (u : ℝ × ℝ) :
    ‖complexFourier (fun p => φ p*replacementExpRemainder (replacementLinear θ e) p)
      ((u.1:ℂ),(u.2:ℂ))‖  ≤
      replacementDecayConstant*replacementP24 φ*x^2*(1+x)^22*Real.exp (2*s*x)/
        (1+max |u.1| |u.2|)^22 := by
  have hg := replacementExpRemainder_smooth (replacementLinear θ e)
  have hb := replacementFourier_decay _ (hφ.mul hg) hc.mul_right
    (2^22*23*replacementP24 φ*(2^24*x^2*(1+x)^22*Real.exp (2*s*x)))
    (by have hP := replacementP24_nonneg φ; positivity)
    (by simpa [replacementDeriv] using replacementAmplitude_L1 φ hφ hc θ e x s hx hs hθ hsupp false 0 (by norm_num))
    (fun j => replacementAmplitude_L1 φ hφ hc θ e x s hx hs hθ hsupp j 22 le_rfl) u
  convert hb using 1 <;> unfold replacementDecayConstant <;> ring

theorem replacementCosh_smooth (θ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (replacementCosh 1 θ) := by
  have he : replacementCosh 1 θ = fun p => (1/8:ℂ)*∑ e : Fin 3 → Bool,
      replacementExpRemainder (replacementLinear θ e) p := funext (replacementCosh_remainders θ)
  rw [he]
  exact contDiff_const.mul (ContDiff.sum (fun e _ => replacementExpRemainder_smooth _))

theorem replacementCosh_fourier_sum (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (θ : Fin 3 → ℝ) (u : ℝ × ℝ) :
    complexFourier (fun p => φ p*replacementCosh 1 θ p) ((u.1:ℂ),(u.2:ℂ)) =
      (1/8:ℂ)*∑ e : Fin 3 → Bool, complexFourier
        (fun p => φ p*replacementExpRemainder (replacementLinear θ e) p) ((u.1:ℂ),(u.2:ℂ)) := by
  let f := fun (e : Fin 3 → Bool) (p : ℝ × ℝ) =>
    φ p*replacementExpRemainder (replacementLinear θ e) p *
      Complex.exp (2*Real.pi*Complex.I*((u.1:ℂ)*p.1+(u.2:ℂ)*p.2))
  have hi (e : Fin 3 → Bool) : Integrable (f e) :=
    complexFourier_integrable (fun p => φ p*replacementExpRemainder (replacementLinear θ e) p)
      (hφ.mul (replacementExpRemainder_smooth (replacementLinear θ e))) hc.mul_right ((u.1:ℂ),(u.2:ℂ))
  calc
    _ = ∫ p, (1/8:ℂ)*∑ e : Fin 3 → Bool, f e p := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [replacementCosh_remainders]
      dsimp [f]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ = _ := by rw [integral_const_mul, integral_finset_sum _ (fun e _ => hi e)]; rfl

theorem replacementCosh_fourier_bound (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (θ : Fin 3 → ℝ) (x s : ℝ)
    (hx : 0 ≤ x) (hs : s ≤ 1) (hθ : ∀ j, |θ j| ≤ x)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (u : ℝ × ℝ) :
    ‖complexFourier (fun p => φ p*replacementCosh 1 θ p) ((u.1:ℂ),(u.2:ℂ))‖ ≤
      replacementDecayConstant*replacementP24 φ*x^2*(1+x)^22*Real.exp (2*s*x)/
        (1+max |u.1| |u.2|)^22 := by
  rw [replacementCosh_fourier_sum φ hφ hc θ u, norm_mul]
  norm_num
  have hb := (norm_sum_le Finset.univ _).trans
    (Finset.sum_le_sum (fun e _ => replacementRemainder_fourier_bound φ hφ hc θ e x s hx hs hθ hsupp u))
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.reducePow, nsmul_eq_mul, Nat.cast_ofNat] at hb
  linarith

end
end HigherCorrelations
