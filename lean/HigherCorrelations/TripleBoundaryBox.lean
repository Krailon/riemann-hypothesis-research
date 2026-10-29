import HigherCorrelations.TripleBoundaryDefinitions
import HigherCorrelations.TripleBoundaryIntegration

/-! UNCONDITIONAL integration of axis and origin boundary layers over a unit
frequency box. The triangle is a subset; its outer margin stays separate. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBoundaryBox_compact : IsCompact tripleBoundaryBox := isCompact_Icc.prod isCompact_Icc

theorem tripleBoundaryBox_measurable : MeasurableSet tripleBoundaryBox :=
  tripleBoundaryBox_compact.isClosed.measurableSet

theorem tripleQuadrantMargin_subset_box (κ : ℝ) (hκ : 0≤κ) :
    tripleQuadrantMargin κ ⊆ tripleBoundaryBox := by
  rintro p ⟨hp,hq,hs⟩
  exact ⟨⟨hp,by linarith⟩,⟨hq,by linarith⟩⟩

theorem tripleBoundary_exp_interval (b : ℝ) (hb : 0<b) :
    (∫ x : ℝ in Icc 0 1, Real.exp (-(b*x))) ≤ 1/b := by
  have hi := tripleBoundary_moment_closed_integrable 0 b hb
  simp only [pow_zero,one_mul] at hi
  have hh := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-(b*x))).le))
    (Filter.Eventually.of_forall (fun x (hx : x ∈ Icc (0:ℝ) 1) => hx.1))
  have he := tripleBoundary_moment_closed 0 b hb
  simp only [pow_zero,one_mul,Nat.factorial_zero,Nat.cast_one,Nat.zero_add,pow_one] at he
  exact hh.trans_eq he

theorem tripleBoundary_axis_box (b : ℝ) (hb : 0<b) :
    (∫ p : ℝ × ℝ in tripleBoundaryBox, Real.exp (-(b*p.1))) ≤ 1/b ∧
    (∫ p : ℝ × ℝ in tripleBoundaryBox, Real.exp (-(b*p.2))) ≤ 1/b := by
  constructor
  · have he := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun x : ℝ => Real.exp (-(b*x))) (fun _ : ℝ => (1:ℝ)) (Icc 0 1) (Icc 0 1)
    simp only [mul_one,integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal,
      max_eq_left (by norm_num : (0:ℝ)≤1),smul_eq_mul,mul_one] at he
    norm_num only [ENNReal.ofReal_one,ENNReal.toReal_one,mul_one,one_mul] at he
    exact (show _ = _ from he).trans_le (tripleBoundary_exp_interval b hb)
  · have he := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun _ : ℝ => (1:ℝ)) (fun x : ℝ => Real.exp (-(b*x))) (Icc 0 1) (Icc 0 1)
    simp only [one_mul,integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal,
      max_eq_left (by norm_num : (0:ℝ)≤1),smul_eq_mul,mul_one,one_mul] at he
    norm_num only [ENNReal.ofReal_one,ENNReal.toReal_one,mul_one,one_mul] at he
    exact (show _ = _ from he).trans_le (tripleBoundary_exp_interval b hb)

theorem tripleBoundary_origin_box (b : ℝ) (hb : 0<b) :
    (∫ p : ℝ × ℝ in tripleBoundaryBox, Real.exp (-(b*p.1))*Real.exp (-(b*p.2))) ≤ 1/b^2 := by
  have hi := tripleBoundary_product_moment_integrable 0 0 b b hb hb
  simp only [pow_zero,one_mul] at hi
  have hh := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun p => by positivity))
    (Filter.Eventually.of_forall (fun p (hp : p ∈ tripleBoundaryBox) =>
      (show p ∈ tripleQuadrant from ⟨hp.1.1,hp.2.1⟩)))
  have he := tripleBoundary_product_moment 0 0 b b hb hb
  simp only [pow_zero,one_mul,Nat.factorial_zero,Nat.cast_one,Nat.zero_add,pow_one] at he
  exact hh.trans_eq (he.trans (by ring))

theorem tripleBoundary_box_envelope (L b : ℝ) (hL : 0≤L) (hb : 0<b) :
    (∫ p : ℝ × ℝ in tripleBoundaryBox,
      L*(Real.exp (-(b*p.1))+Real.exp (-(b*p.2)))+
      L^2*(Real.exp (-(b*p.1))*Real.exp (-(b*p.2)))) ≤ 2*L/b+L^2/b^2 := by
  have hx : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(b*p.1))) tripleBoundaryBox :=
    (by fun_prop : Continuous _).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hy : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(b*p.2))) tripleBoundaryBox :=
    (by fun_prop : Continuous _).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hz : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(b*p.1))*Real.exp (-(b*p.2))) tripleBoundaryBox :=
    (by fun_prop : Continuous _).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hsum : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(b*p.1))+Real.exp (-(b*p.2))) tripleBoundaryBox := hx.add hy
  rw [integral_add (hsum.const_mul L) (hz.const_mul (L^2)),integral_const_mul,
    integral_const_mul,integral_add hx hy]
  obtain ⟨h1,h2⟩ := tripleBoundary_axis_box b hb
  have h3 := tripleBoundary_origin_box b hb
  have hh := add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hL)
    (mul_le_mul_of_nonneg_left h3 (sq_nonneg L))
  convert hh using 1 <;> ring

theorem tripleBoundary_supported_integral (ψ : ℝ × ℝ → ℂ) (f E : ℝ × ℝ → ℝ)
    (M κ : ℝ) (hM : 0≤M) (hκ : 0≤κ)
    (hψ : ∀ p ∈ tripleQuadrant, ‖ψ p‖≤M)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ)
    (hf : ∀ p, 0≤f p) (hE : Continuous E)
    (hE0 : ∀ p ∈ tripleBoundaryBox, 0≤E p)
    (hbound : ∀ p ∈ tripleQuadrantMargin κ, f p≤E p) :
    (∫ p : ℝ × ℝ, ‖tripleQuadrantAmplitude ψ p‖*f p) ≤
      M*(∫ p in tripleBoundaryBox, E p) := by
  have hi : Integrable (tripleBoundaryBox.indicator (fun p => M*E p)) :=
    (hE.const_mul M).continuousOn.integrableOn_compact tripleBoundaryBox_compact
      |>.integrable_indicator tripleBoundaryBox_measurable
  have hp (p : ℝ × ℝ) : ‖tripleQuadrantAmplitude ψ p‖*f p ≤
      tripleBoundaryBox.indicator (fun p => M*E p) p := by
    by_cases hz : tripleQuadrantAmplitude ψ p=0
    · rw [hz,norm_zero,zero_mul]
      by_cases hb : p ∈ tripleBoundaryBox
      · rw [indicator_of_mem hb]
        exact mul_nonneg hM (hE0 p hb)
      · rw [indicator_of_notMem hb]
    · have hmargin := tripleQuadrantAmplitude_support ψ κ hs hz
      have hq : p ∈ tripleQuadrant := ⟨hmargin.1,hmargin.2.1⟩
      rw [indicator_of_mem (tripleQuadrantMargin_subset_box κ hκ hmargin)]
      have hm : ‖tripleQuadrantAmplitude ψ p‖≤M := by
        simpa [tripleQuadrantAmplitude,hq] using hψ p hq
      exact mul_le_mul hm (hbound p hmargin) (hf p) hM
  have hh := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun p => mul_nonneg (norm_nonneg _) (hf p))) hi
    (Filter.Eventually.of_forall hp)
  rwa [integral_indicator tripleBoundaryBox_measurable,integral_const_mul] at hh

theorem tripleBoundary_box_origin_constant (L b d : ℝ) (hb : 0<b) :
    (∫ p : ℝ × ℝ in tripleBoundaryBox,
      L^2*(Real.exp (-((2*b)*p.1))*Real.exp (-((2*b)*p.2)))+d) ≤ L^2/(4*b^2)+d := by
  have hi : IntegrableOn (fun p : ℝ × ℝ =>
      L^2*(Real.exp (-((2*b)*p.1))*Real.exp (-((2*b)*p.2)))) tripleBoundaryBox :=
    (by fun_prop : Continuous _).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hc : IntegrableOn (fun _ : ℝ × ℝ => d) tripleBoundaryBox :=
    continuous_const.continuousOn.integrableOn_compact tripleBoundaryBox_compact
  rw [integral_add hi hc,integral_const_mul]
  have hm : (volume : Measure (ℝ × ℝ)) tripleBoundaryBox=1 := by
    rw [tripleBoundaryBox,Measure.volume_eq_prod,Measure.prod_prod]
    norm_num [Real.volume_Icc]
  have he : (∫ _p : ℝ × ℝ in tripleBoundaryBox, d)=d := by simp [setIntegral_const,hm,Measure.real]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (tripleBoundary_origin_box (2*b) (by positivity)) (sq_nonneg L)
  convert add_le_add hh (le_refl d) using 1 <;> ring

theorem tripleBoundary_box_axis_sum (b : ℝ) (hb : 0<b) :
    (∫ p : ℝ × ℝ in tripleBoundaryBox,
      Real.exp (-(b*p.1))+Real.exp (-(b*p.2))) ≤ 2/b := by
  have hx : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(b*p.1))) tripleBoundaryBox :=
    (by fun_prop : Continuous _).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  have hy : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(b*p.2))) tripleBoundaryBox :=
    (by fun_prop : Continuous _).continuousOn.integrableOn_compact tripleBoundaryBox_compact
  rw [integral_add hx hy]
  obtain ⟨h1,h2⟩ := tripleBoundary_axis_box b hb
  convert add_le_add h1 h2 using 1 <;> ring

end
end HigherCorrelations
