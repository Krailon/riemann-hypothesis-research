import HigherCorrelations.ComplexFourierDefinitions
import HigherCorrelations.CompactFourierFamily

/-! Bounded-imaginary-strip decay in the exact project convention. UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap

@[simp] theorem planeCoords_apply (ξ : FourierPlane) : planeCoords ξ = WithLp.ofLp ξ := rfl

theorem complexFourier_integrable (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (z : ℂ × ℂ) :
    Integrable (fun ξ : ℝ × ℝ => φ ξ * Complex.exp
      (2 * Real.pi * Complex.I * (z.1 * ξ.1 + z.2 * ξ.2))) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact hφ.continuous.mul (by fun_prop)
  · exact hc.mul_right

theorem complexFourier_eq_inverse (φ : ℝ × ℝ → ℂ) (x y : ℝ × ℝ) :
    complexFourier φ (complexPair x y) = 𝓕⁻ (twistedAmplitude φ y) (WithLp.toLp 2 x) := by
  rw [Real.fourierInv_eq']
  have hm := (WithLp.volume_preserving_ofLp ℝ ℝ).integral_comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toHomeomorph.measurableEmbedding
    (fun ξ : ℝ × ℝ => φ ξ * Complex.exp
      (2 * Real.pi * Complex.I * ((complexPair x y).1 * ξ.1 + (complexPair x y).2 * ξ.2)))
  unfold complexFourier
  rw [← hm]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [twistedAmplitude, planeCoords_apply,
    WithLp.prod_inner_apply, Real.inner_apply, smul_eq_mul, complexPair,
    Complex.ofReal_mul, Complex.ofReal_add]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem complexFourier_real_eq_inverse (φ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    complexFourier φ ((x.1 : ℂ), (x.2 : ℂ)) =
      𝓕⁻ (fun ξ : FourierPlane => φ (WithLp.ofLp ξ)) (WithLp.toLp 2 x) := by
  have ht : twistedAmplitude φ (0, 0) = (fun ξ : FourierPlane => φ (WithLp.ofLp ξ)) := by
    funext ξ
    simp [twistedAmplitude]
  simpa only [complexPair, Complex.ofReal_zero, mul_zero, sub_zero, ht] using complexFourier_eq_inverse φ x (0, 0)

theorem complexFourier_strip_decay (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (B : ℝ) (_hB : 0 ≤ B) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ × ℝ, |y.1| ≤ B → |y.2| ≤ B →
      ‖complexFourier φ (complexPair x y)‖ ≤ C / (1 + max |x.1| |x.2|) ^ n := by
  have hs : ContDiff ℝ ∞ (Function.uncurry (twistedAmplitude φ)) := by
    have hp : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × FourierPlane => planeCoords p.2) :=
      planeCoords.contDiff.comp contDiff_snd
    have he : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × FourierPlane =>
        (p.1.1 : ℂ) * (planeCoords p.2).1 + (p.1.2 : ℂ) * (planeCoords p.2).2) :=
      ((Complex.ofRealCLM.contDiff.comp contDiff_fst.fst).mul
        (Complex.ofRealCLM.contDiff.comp hp.fst)).add
      ((Complex.ofRealCLM.contDiff.comp contDiff_fst.snd).mul
        (Complex.ofRealCLM.contDiff.comp hp.snd))
    exact (hφ.comp hp).mul (Complex.contDiff_exp.comp (contDiff_const.mul he))
  let K : Set FourierPlane := planeCoords ⁻¹' tsupport φ
  have hK : IsCompact K := planeCoords.toHomeomorph.isClosedEmbedding.isCompact_preimage hc
  have hsupp : ∀ y, Function.support (twistedAmplitude φ y) ⊆ K := by
    intro y ξ hξ
    exact subset_tsupport φ (mul_ne_zero_iff.mp hξ).1
  let J := Set.Icc (-B) B ×ˢ Set.Icc (-B) B
  obtain ⟨C, hC, hb⟩ := compact_family_fourier_decay (twistedAmplitude φ) hs K hK hsupp J
    (isCompact_Icc.prod isCompact_Icc) n
  refine ⟨C, hC, ?_⟩
  intro x y hy₁ hy₂
  rw [complexFourier_eq_inverse, Real.fourierInv_eq_fourier_neg]
  have hh := hb y ⟨abs_le.mp hy₁, abs_le.mp hy₂⟩ (-(WithLp.toLp 2 x))
  rw [norm_neg] at hh
  apply hh.trans
  have hm : max |x.1| |x.2| ≤ ‖WithLp.toLp 2 x‖ := by
    apply max_le
    · exact WithLp.norm_fst_le ℝ (WithLp.toLp 2 x)
    · exact WithLp.norm_snd_le ℝ (WithLp.toLp 2 x)
  exact div_le_div_of_nonneg_left hC.le (by positivity)
    (pow_le_pow_left₀ (by positivity) (by linarith) n)

end
end HigherCorrelations
