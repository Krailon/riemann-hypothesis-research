import HigherCorrelations.UniformHeightMass
import HigherCorrelations.RationalTransfer

/-! UNCONDITIONAL specializations. The real-test envelope is an explicit hypothesis;
no signed complex-argument cancellation is asserted. -/
namespace HigherCorrelations
noncomputable section

theorem anchored_decay_twentieth_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a → 0 ≤ A →
      ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^20) →
      normalizedTripleTail T a ((Real.log T)^(1/4:ℝ)) f ≤ C*A/(Real.log T)^2 := by
  obtain ⟨C,hC,hb⟩ := anchored_decay_strict_tail_uniform 20 (by norm_num)
  refine ⟨C,hC,fun T a A hT ha hA f hf => ?_⟩
  have hq := (uniformHeightThreshold_bounds hT).2.1
  have hq0 : 0 < Real.log T := by linarith
  have hr : 0 < (Real.log T)^(1/4:ℝ) := Real.rpow_pos_of_pos hq0 _
  have he : ((Real.log T)^(1/4:ℝ))^16 = (Real.log T)^4 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hq0.le]
    norm_num
  have hh := hb T a _ A hT ha hr.le hA f hf
  norm_num at hh
  calc
    _ ≤ C*A*(Real.log T)^2/((Real.log T)^(1/4:ℝ))^16 := hh.trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hr.le (by linarith) _))
    _ = C*A/(Real.log T)^2 := by rw [he]; field_simp

theorem bounded_multiplier_mass_tail (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A B : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a →
      0 ≤ A → 0 ≤ B → ∀ f k : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) → (∀ t, ‖k t‖ ≤ B) →
      Summable (fun t => ‖k t*f t‖) ∧
      normalizedTripleMass T (fun t => k t*f t) ≤ C*B*A*(Real.log T)^2 ∧
      ∀ R : ℝ, 0 ≤ R → normalizedTripleTail T a R (fun t => k t*f t) ≤
        C*B*A*(Real.log T)^2/(1+R)^(p-4) := by
  obtain ⟨C₁,h₁,b₁⟩ := anchored_decay_mass_uniform p hp
  obtain ⟨C₂,h₂,b₂⟩ := anchored_decay_strict_tail_uniform p hp
  refine ⟨C₁+C₂,by positivity,fun T a A B hT ha hA hB f k hf hk => ?_⟩
  have hd := bounded_factor_decay (anchoredRadius T a) f k A B hA hB p hk hf
  have hm := b₁ T a (B*A) hT ha (mul_nonneg hB hA) _ hd
  refine ⟨hm.1,?_,fun R hR => ?_⟩
  · nlinarith [hm.2,mul_nonneg h₂.le (mul_nonneg (mul_nonneg hB hA) (sq_nonneg (Real.log T)))]
  · have hh := b₂ T a R (B*A) hT ha hR (mul_nonneg hB hA) _ hd
    apply hh.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg h₁.le (mul_nonneg (mul_nonneg hB hA) (sq_nonneg (Real.log T)))]

theorem actual_kernel_uniform_bounds (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a → 0 ≤ A →
      ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      let g := fun t => actualRationalKernel (anchoredToTriple t)*f t
      Summable (fun t => ‖g t‖) ∧ normalizedTripleMass T g ≤ C*A*(Real.log T)^2 ∧
      ∀ R : ℝ, 0 ≤ R → normalizedTripleTail T a R g ≤ C*A*(Real.log T)^2/(1+R)^(p-4) := by
  obtain ⟨C,hC,hb⟩ := bounded_multiplier_mass_tail p hp
  refine ⟨C*(7*Real.pi/9),by positivity,fun T a A hT ha hA f hf => ?_⟩
  exact hb T a A (7*Real.pi/9) hT ha hA (by positivity) f
    (fun t => actualRationalKernel (anchoredToTriple t)) hf (fun t => actualRationalKernel_bound _)

theorem actual_horizontal_uniform_bounds (js : List (Fin 3)) (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a → 0 ≤ A →
      ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      let g := fun t => horizontalPartial js
        (horizontalProfile (actualProfileGap (anchoredToTriple t) 1) (actualProfileGap (anchoredToTriple t) 2))
        (actualProfileParameters (anchoredToTriple t))*f t
      Summable (fun t => ‖g t‖) ∧ normalizedTripleMass T g ≤ C*A*(Real.log T)^2 ∧
      ∀ R : ℝ, 0 ≤ R → normalizedTripleTail T a R g ≤ C*A*(Real.log T)^2/(1+R)^(p-4) := by
  obtain ⟨C,hC,hb⟩ := bounded_multiplier_mass_tail p hp
  have hd : 0 < profileDerivativeBound js.length := by unfold profileDerivativeBound; positivity
  refine ⟨C*profileDerivativeBound js.length,by positivity,fun T a A hT ha hA f hf => ?_⟩
  exact hb T a A _ hT ha hA hd.le f _ hf (fun t => actualProfile_horizontal_bound js _)

theorem meanSpacing_log_comparison {T : ℝ} (hT : uniformHeightThreshold ≤ T) :
    Real.log T ≤ 4*Real.pi*meanSpacing T := by
  obtain ⟨ht,hq,hm⟩ := uniformHeightThreshold_bounds hT
  have hp := Real.pi_pos
  have hl : Real.log (2*Real.pi) ≤ 2*Real.pi := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  unfold meanSpacing at hm ⊢
  rw [Real.log_div (by positivity) (by positivity)] at hm ⊢
  have hh := (le_div_iff₀ (show 0<2*Real.pi by positivity)).mp hm
  field_simp
  rw [mul_comm Real.pi 2]
  linarith

theorem transferCoefficient_mass_bound (T : ℝ) (hT : uniformHeightThreshold ≤ T)
    (f : AnchoredTriple T → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    ‖transferCoefficient T*(∑' t, f t)‖ ≤ (16/3)*normalizedTripleMass T f := by
  obtain ⟨ht,hq,_⟩ := uniformHeightThreshold_bounds hT
  have ht0 : 0 ≤ T := by linarith
  have hq0 : 0 ≤ Real.log T := by linarith
  have hc : ‖transferCoefficient T‖ = 16/(3*T*Real.log T) := by
    simp [transferCoefficient,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0,abs_of_nonneg hq0]
  rw [norm_mul,hc]
  calc
    _ ≤ (16/(3*T*Real.log T))*(∑' t, ‖f t‖) := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hf) (by positivity)
    _ = _ := by unfold normalizedTripleMass; ring

theorem ordinateCoefficient_mass_bound (T : ℝ) (hT : uniformHeightThreshold ≤ T)
    (f : AnchoredTriple T → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    ‖ordinateCoefficient T*(∑' t, f t)‖ ≤ (4*Real.pi)*normalizedTripleMass T f := by
  obtain ⟨ht,hq,hm⟩ := uniformHeightThreshold_bounds hT
  have ht0 : 0 < T := by linarith
  have hq0 : 0 < Real.log T := by linarith
  have hm0 : 0 < meanSpacing T := by linarith
  have hc : ‖ordinateCoefficient T‖ = 1/(T*meanSpacing T) := by
    simp [ordinateCoefficient,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0,abs_of_pos hm0]
  have hb : 1/(T*meanSpacing T) ≤ (4*Real.pi)/(T*Real.log T) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left (meanSpacing_log_comparison hT) ht0.le
    nlinarith
  rw [norm_mul,hc]
  calc
    _ ≤ (4*Real.pi)/(T*Real.log T)*(∑' t, ‖f t‖) := mul_le_mul hb (norm_tsum_le_tsum_norm hf) (norm_nonneg _) (by positivity)
    _ = _ := by unfold normalizedTripleMass; ring

end
end HigherCorrelations
