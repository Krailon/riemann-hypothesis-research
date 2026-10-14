import HigherCorrelations.PairHorizontalBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A polynomial envelope for the good-height horizontal integrands. UNCONDITIONAL.
The exponent 7/4 leaves decay against the quadratic contour kernel. -/
namespace HigherCorrelations
noncomputable section
open Complex Filter
open scoped Topology

private theorem horizontal_envelope_power (D r A B Q G C : ℝ)
    (hD : 0 ≤ D) (hr : 0 < r) (hA : 0 < A) (hB : 0 ≤ B)
    (hQ : 0 ≤ Q) (hG : 0 < G) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R →
      D + ((A*(1+4*R)^(3/2:ℝ)+B)/Real.log 2)*(C*Real.log R+1/r) + 2*R*Q +
        1 + |Real.log Real.pi|/2 + G*Real.log R/2 ≤ K*R^(7/4:ℝ) := by
  let E := (A*(5:ℝ)^(3/2:ℝ)+B)/Real.log 2
  let F := 4*C+1/r
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨D+E*F+2*Q+1+|Real.log Real.pi|/2+2*G,
    by positivity,fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  have hp := Real.one_le_rpow hR (by norm_num : (0:ℝ)≤3/2)
  have hq := Real.one_le_rpow hR (by norm_num : (0:ℝ)≤1/4)
  have hw := Real.one_le_rpow hR (by norm_num : (0:ℝ)≤7/4)
  have hpw : R^(1/4:ℝ) ≤ R^(7/4:ℝ) := Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hrw : R ≤ R^(7/4:ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (1:ℝ)≤7/4)
  have hlog : Real.log R ≤ 4*R^(1/4:ℝ) := by
    have h := Real.log_le_rpow_div hR0.le (by norm_num : (0:ℝ)<1/4)
    linarith
  have hb : (A*(1+4*R)^(3/2:ℝ)+B)/Real.log 2 ≤ E*R^(3/2:ℝ) := by
    have hp' : (1+4*R)^(3/2:ℝ) ≤ (5*R)^(3/2:ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤5) hR0.le] at hp'
    have hm := mul_le_mul_of_nonneg_left hp' hA.le
    have hB' := mul_le_mul_of_nonneg_left hp hB
    dsimp [E]
    apply (div_le_div_of_nonneg_right (add_le_add hm (by simpa using hB'))
      (Real.log_nonneg (by norm_num : (1:ℝ)≤2))).trans_eq
    ring
  have hc : C*Real.log R+1/r ≤ F*R^(1/4:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog hC.le
    have hr' := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 1/r)
    dsimp [F]
    nlinarith
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hm := mul_le_mul hb hc (by positivity : 0 ≤ C*Real.log R+1/r)
    (mul_nonneg hE (Real.rpow_nonneg hR0.le _))
  have he : (E*R^(3/2:ℝ))*(F*R^(1/4:ℝ)) = E*F*R^(7/4:ℝ) := by
    rw [show (7/4:ℝ) = 3/2+1/4 by norm_num, Real.rpow_add hR0]
    ring
  rw [he] at hm
  have hg := mul_le_mul_of_nonneg_left (hlog.trans (mul_le_mul_of_nonneg_left hpw (by norm_num))) hG.le
  have hd := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ D+1+|Real.log Real.pi|/2)
  have hqr := mul_le_mul_of_nonneg_left hrw (by positivity : 0 ≤ 2*Q)
  nlinarith

theorem pairZeta_goodHeight_power (M : ℕ) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (H U σ : ℝ), 2*(M:ℝ)+6 ≤ H → H ≤ |U| → |U| ≤ H+1 →
      -(2*(M:ℝ)+1) ≤ σ → σ ≤ 5/2 →
      (∀ i : ZeroOccurrence, 1/(C*Real.log (H+4)) ≤ |U-occurrenceOrdinate i|) →
      ‖-deriv riemannZeta ((σ:ℂ)+(U:ℂ)*I) / riemannZeta ((σ:ℂ)+(U:ℂ)*I)‖ ≤
        K*(2*H)^(7/4:ℝ) := by
  obtain ⟨D,r,A,B,Q,G,hD,hr,hA,hB,hQ,hG,hbound⟩ := pairZeta_horizontal_majorant M
  obtain ⟨K,hK,hpower⟩ := horizontal_envelope_power D r A B Q G C hD hr hA hB hQ hG hC
  refine ⟨K,hK,fun H U σ hH hU hU' hσ hσ' hgap => ?_⟩
  have hM := Nat.cast_nonneg (α:=ℝ) M
  have hH0 : 0 < H := by linarith
  have hR : 1 ≤ 2*H := by linarith
  have hlog : 0 < Real.log (H+4) := Real.log_pos (by linarith)
  have hz : ‖(σ:ℂ)+(U:ℂ)*I‖ ≤ 2*H := by
    have hh := norm_add_le (σ:ℂ) ((U:ℂ)*I)
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hh
    have hs : |σ| ≤ 2*(M:ℝ)+3 := abs_le.mpr ⟨by linarith,by linarith⟩
    linarith
  have hb := hbound σ U (2*H) (1/(C*Real.log (H+4))) hσ hσ'
    (by linarith) hR hz (by positivity) hgap
  have he : 1/(1/(C*Real.log (H+4))) = C*Real.log (H+4) := by simp
  rw [he] at hb
  apply hb.trans
  apply le_trans _ (hpower (2*H) hR)
  have hlH : Real.log (H+4) ≤ Real.log (2*H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlU : Real.log (|U|+2) ≤ Real.log (2*H) :=
    Real.log_le_log (by linarith) (by linarith)
  gcongr

/-- A uniform horizontal integrand bound for either sign of a good height. -/
theorem pairContourIntegrand_goodHeight_bound (M : ℕ) (C X t : ℝ)
    (hC : 0 < C) (hX : 1 ≤ X) :
    ∃ K : ℝ, 0 < K ∧ ∀ H U σ : ℝ,
      2*(M:ℝ)+6 ≤ H → 2*|t|+2 ≤ H → H ≤ |U| → |U| ≤ H+1 →
      -(2*(M:ℝ)+1) ≤ σ → σ ≤ 5/2 →
      (∀ i : ZeroOccurrence, 1/(C*Real.log (H+4)) ≤ |U-occurrenceOrdinate i|) →
      ‖pairContourIntegrand X t ((σ:ℂ)+(U:ℂ)*I)‖ ≤ K*H^(-(1/4:ℝ)) := by
  obtain ⟨A,hA,ha⟩ := pairZeta_goodHeight_power M C hC
  refine ⟨8*X^2*A*2^(7/4:ℝ),by positivity,fun H U σ hH ht hU hU' hσ hσ' hgap => ?_⟩
  have hH0 : 0 < H := by have := Nat.cast_nonneg (α:=ℝ) M; linarith
  have hd : H/2 ≤ |U-t| := by
    have hh := abs_add_le (U-t) t
    rw [sub_add_cancel] at hh
    linarith
  have hd0 : U-t ≠ 0 := by intro he; rw [he,abs_zero] at hd; linarith
  have hk := pairContourKernel_horizontal_bound X t σ U hX hσ' hd0
  have hk' : ‖pairContourKernel X t ((σ:ℂ)+(U:ℂ)*I)‖ ≤ 8*X^2/H^2 := by
    apply hk.trans
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hd0) (sq_pos_of_pos hH0)).mpr
    have hh : H^2 ≤ 4*(U-t)^2 := by nlinarith [sq_abs (U-t)]
    nlinarith [sq_nonneg X]
  have hb := mul_le_mul (ha H U σ hH hU hU' hσ hσ' hgap) hk'
    (norm_nonneg _) (by positivity : 0 ≤ A*(2*H)^(7/4:ℝ))
  change ‖(-deriv riemannZeta ((σ:ℂ)+(U:ℂ)*I) / riemannZeta ((σ:ℂ)+(U:ℂ)*I)) *
    pairContourKernel X t ((σ:ℂ)+(U:ℂ)*I)‖ ≤ _
  rw [norm_mul]
  apply hb.trans_eq
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hH0.le]
  have he : H^(7/4:ℝ)/H^2 = H^(-(1/4:ℝ)) := by
    rw [← Real.rpow_natCast H 2, ← Real.rpow_sub hH0]
    norm_num
  calc
    _ = (8*X^2*A*2^(7/4:ℝ))*(H^(7/4:ℝ)/H^2) := by ring
    _ = _ := by rw [he]

/-- Horizontal edges vanish along any signed sequence satisfying the quantified gap.
The strip, X, and t are fixed before the height tends to infinity. -/
theorem pairContour_horizontal_tendsto (M : ℕ) (C X t : ℝ)
    (hC : 0 < C) (hX : 1 ≤ X) (U : ℕ → ℝ)
    (hU : ∀ n : ℕ, (n:ℝ)+2 ≤ |U n| ∧ |U n| ≤ (n:ℝ)+3)
    (hgap : ∀ (n : ℕ) (i : ZeroOccurrence),
      1/(C*Real.log ((n:ℝ)+6)) ≤ |U n-occurrenceOrdinate i|) :
    Tendsto (fun n => ∫ σ in -(2*(M:ℝ)+1)..(5/2:ℝ),
      pairContourIntegrand X t ((σ:ℂ)+(U n:ℂ)*I)) atTop (𝓝 0) := by
  obtain ⟨K,hK,hbound⟩ := pairContourIntegrand_goodHeight_bound M C X t hC hX
  have hheight : Tendsto (fun n : ℕ => (n:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ =>
      (K*((n:ℝ)+2)^(-(1/4:ℝ))) * |(5/2:ℝ)-(-(2*(M:ℝ)+1))|) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp
      hheight).const_mul K |>.mul_const |(5/2:ℝ)-(-(2*(M:ℝ)+1))|
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hheight.eventually_ge_atTop (2*(M:ℝ)+6),
    hheight.eventually_ge_atTop (2*|t|+2)] with n hn ht
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  have hlo : -(2*(M:ℝ)+1) ≤ (5/2:ℝ) := by have := Nat.cast_nonneg (α:=ℝ) M; linarith
  rw [Set.uIoc_of_le hlo] at hσ
  apply hbound ((n:ℝ)+2) (U n) σ hn ht (hU n).1 (by linarith [(hU n).2])
    hσ.1.le hσ.2
  intro i
  convert hgap n i using 1 <;> ring

end
end HigherCorrelations
