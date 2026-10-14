import HigherCorrelations.PairFiniteRectangle
import HigherCorrelations.PairHorizontalDecay
import HigherCorrelations.PairLeftDecay
import HigherCorrelations.PairEulerContour

/-! UNCONDITIONAL rectangle boundary limits; height first, then the left shift. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

def pairLeftIntegral (X t : ℝ) (M : ℕ) : ℂ :=
  (1/(2*(Real.pi:ℂ)))*(∫ v : ℝ, pairContourIntegrand X t (-(2*(M:ℂ)+1)+(v:ℂ)*I))

theorem pairContour_right_integrable (X t : ℝ) (hX : 0 < X) :
    Integrable (fun v : ℝ => pairContourIntegrand X t (5/2+(v:ℂ)*I)) := by
  obtain ⟨C,hC,hb⟩ := pairZeta_logDeriv_right_bound
  apply ((integrable_inv_one_add_sq.comp_sub_right t).const_mul (C*(2*X^2))).mono'
  · exact ((pairContourIntegrand_measurable X t).comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with v
    have h₁ := hb (5/2+(v:ℂ)*I) (by norm_num)
    have h₂ : ‖pairContourKernel X t (5/2+(v:ℂ)*I)‖ ≤ 2*X^2/(1+(v-t)^2) := by
      rw [pairContourKernel_right]
      exact pairedMellinIntegrand_bound X (v-t) hX
    unfold pairContourIntegrand
    rw [norm_mul]
    apply (mul_le_mul h₁ h₂ (norm_nonneg _) hC).trans_eq
    ring

theorem pairLeftIntegral_tendsto (X t : ℝ) (hX : 1 < X) :
    Tendsto (pairLeftIntegral X t) atTop (𝓝 0) := by
  change Tendsto (fun M : ℕ => (1/(2*(Real.pi:ℂ)))*(∫ v : ℝ,
    pairContourIntegrand X t (-(2*(M:ℂ)+1)+(v:ℂ)*I))) atTop (𝓝 0)
  simpa only [mul_zero] using (pairContour_left_tendsto X t hX).const_mul (1/(2*(Real.pi:ℂ)))

theorem pairRectangle_height_tendsto (X t C : ℝ) (M : ℕ) (hX : 1 ≤ X) (hC : 0 < C)
    (U : ℕ → ℝ) (hU : ∀ n : ℕ, (n:ℝ)+2 < U n ∧ U n < (n:ℝ)+3)
    (hUt : Tendsto U atTop atTop)
    (hgap : ∀ (n : ℕ) (i : ZeroOccurrence),
      1/(C*Real.log ((n:ℝ)+6)) ≤ |U n-occurrenceOrdinate i| ∧
      1/(C*Real.log ((n:ℝ)+6)) ≤ |-U n-occurrenceOrdinate i|) :
    Tendsto (fun n => RectangleIntegral' (pairContourIntegrand X t)
      (pairRectangleLeft M (U n)) (pairRectangleRight (U n))) atTop
      (𝓝 (pairRightIntegral (X,t)-pairLeftIntegral X t M)) := by
  have hpos (n : ℕ) : 0 ≤ U n := by have := Nat.cast_nonneg (α:=ℝ) n; linarith [(hU n).1]
  have htop := pairContour_horizontal_tendsto M C X t hC hX U
    (fun n => by rw [abs_of_nonneg (hpos n)]; exact ⟨(hU n).1.le,(hU n).2.le⟩)
    (fun n i => (hgap n i).1)
  have hbottom := pairContour_horizontal_tendsto M C X t hC hX (fun n => -U n)
    (fun n => by rw [abs_neg,abs_of_nonneg (hpos n)]; exact ⟨(hU n).1.le,(hU n).2.le⟩)
    (fun n i => (hgap n i).2)
  have hright := intervalIntegral_tendsto_integral (pairContour_right_integrable X t (by linarith))
    (tendsto_neg_atTop_atBot.comp hUt) hUt
  have hleft := intervalIntegral_tendsto_integral (pairContour_left_integrable X t M)
    (tendsto_neg_atTop_atBot.comp hUt) hUt
  have hh := (((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)).const_smul
    (1/(2*(Real.pi:ℂ)*I))
  convert hh using 1
  · ext n
    simp [RectangleIntegral',RectangleIntegral,HIntegral,VIntegral,pairRectangleLeft,pairRectangleRight]
  · simp only [sub_zero,zero_add,smul_eq_mul,pairRightIntegral,pairLeftIntegral]
    congr 1
    have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi,Complex.I_ne_zero]
    <;> simp only [mul_comm]
    <;> ring

end
end HigherCorrelations
