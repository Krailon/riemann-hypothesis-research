import HigherCorrelations.PairFourierPeak
import HigherCorrelations.PairFourierScaling
import HigherCorrelations.PairFourierBookkeeping
import HigherCorrelations.PairAsymptotic

/-! UNCONDITIONAL Fourier test passage. The normalized asymptotic inherits the
pinned PREPRINT input; exact translation and approximate-identity facts do not.
Fix the test before T tends to infinity. All complex zero arguments are retained. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

theorem pairFourierPeak_power (T a : ℝ) (hT : 0<T) :
    pairFourierPeak (Real.log T) a = T^(-2*|a|)*Real.log T := by
  rw [Real.rpow_def_of_pos hT]
  unfold pairFourierPeak
  rw [show -2*Real.log T*|a| = Real.log T*(-2*|a|) by ring]
  ring

theorem pairFourier_integrated_error (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hs : Function.support g ⊆ Icc (-1) 1)
    (M A B T : ℝ) (hM : ∀ a, ‖g a‖≤M) (hA : 0≤A) (_hB : 0≤B) (hT : 3≤T)
    (hF : ∀ a : ℝ, |a|≤1 →
      |pairNormalizedCorrelation T a-T^(-2*|a|)*Real.log T-(|a|)| ≤
        A*T^(-2*|a|)+B/Real.sqrt (Real.log T)) :
    ‖pairFourierStatistic T g-
      (∫ a : ℝ, g a*(pairFourierPeak (Real.log T) a : ℂ))-
      (∫ a : ℝ, (|a| : ℝ)*g a)‖ ≤
        A*M/Real.log T+B*(∫ a : ℝ, ‖g a‖)/Real.sqrt (Real.log T) := by
  have ht : 0<T := by linarith
  have hq : 0<Real.log T := Real.log_pos (by linarith)
  have hm : 0≤M := (norm_nonneg (g 0)).trans (hM 0)
  have hi := pairFourierStatistic_integrable g hg hc T ht
  have hp : Integrable (fun a => g a*(pairFourierPeak (Real.log T) a : ℂ)) :=
    (hg.mul (by unfold pairFourierPeak; fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have ha : Integrable (fun a : ℝ => (|a| : ℝ)*g a) :=
    ((by fun_prop : Continuous (fun a : ℝ => ((|a| : ℝ):ℂ))).mul hg).integrable_of_hasCompactSupport hc.mul_left
  have hd : ∀ a : ℝ,
      ‖g a*(pairNormalizedCorrelation T a : ℂ)-g a*(pairFourierPeak (Real.log T) a : ℂ)-(|a| : ℝ)*g a‖ ≤
      (A*M/Real.log T)*pairFourierPeak (Real.log T) a+B/Real.sqrt (Real.log T)*‖g a‖ := by
    intro a
    by_cases hga : g a=0
    · simp only [hga,zero_mul,mul_zero,sub_self,norm_zero,add_zero]
      exact mul_nonneg (by positivity) (pairFourierPeak_nonneg _ _ hq.le)
    have has : |a|≤1 := abs_le.mpr (hs hga)
    have hf := hF a has
    have he : g a*(pairNormalizedCorrelation T a : ℂ)-g a*(pairFourierPeak (Real.log T) a : ℂ)-(|a| : ℝ)*g a =
        g a*((pairNormalizedCorrelation T a-T^(-2*|a|)*Real.log T-(|a|) : ℝ):ℂ) := by
      rw [pairFourierPeak_power T a ht]; push_cast; ring
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ ‖g a‖*(A*T^(-2*|a|)+B/Real.sqrt (Real.log T)) := mul_le_mul_of_nonneg_left hf (norm_nonneg _)
      _ ≤ M*(A*T^(-2*|a|))+B/Real.sqrt (Real.log T)*‖g a‖ := by
        nlinarith [mul_le_mul_of_nonneg_right (hM a) (show 0≤A*T^(-2*|a|) by positivity)]
      _ = _ := by rw [pairFourierPeak_power T a ht]; field_simp
  have hid : Integrable (fun a => g a*(pairNormalizedCorrelation T a : ℂ)-g a*(pairFourierPeak (Real.log T) a : ℂ)) := hi.sub hp
  rw [pairFourierStatistic_identity g hg hc T hT,← integral_sub hi hp,← integral_sub hid ha]
  calc
    _ ≤ ∫ a : ℝ, (A*M/Real.log T)*pairFourierPeak (Real.log T) a+B/Real.sqrt (Real.log T)*‖g a‖ :=
      norm_integral_le_of_norm_le
        (((pairFourierPeak_integrable _ hq).const_mul _).add
          ((hg.integrable_of_hasCompactSupport hc).norm.const_mul _)) (Eventually.of_forall hd)
    _ = _ := by
      rw [integral_add ((pairFourierPeak_integrable _ hq).const_mul _)
        ((hg.integrable_of_hasCompactSupport hc).norm.const_mul _),integral_const_mul,integral_const_mul,
        pairFourierPeak_mass _ hq]
      ring

theorem pairFourier_named_error_budget :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ (g : ℝ → ℂ), Continuous g → HasCompactSupport g →
      Function.support g ⊆ Icc (-1) 1 → ∀ M₀ M₁ : ℝ,
      (∀ a, ‖g a‖≤M₀) → (∀ a : ℝ, ‖g a-g 0‖≤M₁*|a|) → ∀ T : ℝ, 3≤T →
      ‖pairFourierStatistic T g-pairFourierMain g‖ ≤
        (A*M₀+M₁/2)/Real.log T+B*(∫ a : ℝ, ‖g a‖)/Real.sqrt (Real.log T) := by
  obtain ⟨A,B,hA,hB,hF⟩ := pairNormalized_asymptotic
  refine ⟨A,B,hA,hB,fun g hg hc hs M₀ M₁ hM₀ hM₁ T hT => ?_⟩
  have hq : 0<Real.log T := Real.log_pos (by linarith)
  have he := pairFourier_integrated_error g hg hc hs M₀ A B T hM₀ hA.le hB.le hT (hF T · hT)
  have hp := pairFourierPeak_approximation g hg hc M₁ hM₁ (Real.log T) hq
  have hd : pairFourierStatistic T g-pairFourierMain g =
      (pairFourierStatistic T g-(∫ a : ℝ, g a*(pairFourierPeak (Real.log T) a : ℂ))-
        (∫ a : ℝ, (|a| : ℝ)*g a))+
      ((∫ a : ℝ, g a*(pairFourierPeak (Real.log T) a : ℂ))-g 0) := by
    unfold pairFourierMain; ring
  rw [hd]
  exact (norm_add_le _ _).trans ((add_le_add he hp).trans_eq (by ring))

theorem pairFourier_asymptotic (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : Function.support g ⊆ Icc (-1) 1) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 3≤T →
      ‖pairFourierStatistic T g-pairFourierMain g‖≤C/Real.sqrt (Real.log T) := by
  obtain ⟨A,B,hA,hB,h⟩ := pairFourier_named_error_budget
  obtain ⟨M₀,M₁,hM₀,hM₁,hg₀,hg₁,hg₂⟩ := pairFourierTest_bounds g hg hc
  let D := A*M₀+M₁/2
  let J := ∫ a : ℝ, ‖g a‖
  have hd : 0≤D := by dsimp [D]; positivity
  have hj : 0≤J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨D+B*J+1,by positivity,fun T hT => ?_⟩
  have he := h g hg.continuous hc hs M₀ M₁ hg₀ hg₂ T hT
  have hq := (pairRHS_log_comparison T hT).1
  have hq0 : 0<Real.log T := by linarith
  have hsq : Real.sqrt (Real.log T)≤Real.log T := by
    nlinarith [Real.sq_sqrt hq0.le,Real.sqrt_nonneg (Real.log T)]
  have hsq0 : 0<Real.sqrt (Real.log T) := Real.sqrt_pos.mpr hq0
  calc
    _ ≤ D/Real.log T+B*J/Real.sqrt (Real.log T) := he
    _ ≤ D/Real.sqrt (Real.log T)+B*J/Real.sqrt (Real.log T) :=
      add_le_add (div_le_div_of_nonneg_left hd hsq0 hsq) le_rfl
    _ ≤ (D+B*J+1)/Real.sqrt (Real.log T) := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hsq0.le

theorem pairFourier_tendsto (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : Function.support g ⊆ Icc (-1) 1) :
    Tendsto (fun T : ℝ => pairFourierStatistic T g) atTop (𝓝 (pairFourierMain g)) := by
  obtain ⟨C,hC,h⟩ := pairFourier_asymptotic g hg hc hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz : Tendsto (fun T : ℝ => C/Real.sqrt (Real.log T)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  exact squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _))
    ((eventually_ge_atTop (3:ℝ)).mono (fun T hT => h T hT)) hz

end
end HigherCorrelations
