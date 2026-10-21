import HigherCorrelations.PairZeroTruncBound
import HigherCorrelations.PairZeroBoundaryIntegrals

/-! UNCONDITIONAL finite-height replacement. The omitted occurrences are outside
(0,T]; only occurrences in the retained cutoff receive horizontal weights. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairZeroHeightError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
      |pairZeroHeightError X T Z| ≤ C*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^3 := by
  obtain ⟨G,hG,hg⟩ := zeroKernel_summable_bound
  obtain ⟨D,hD,hd⟩ := zeroKernel_exterior_bound
  let K := 2*(4/3:ℝ)^2*G*D
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨64*K,by positivity,fun X T Z hX hT hZ => ?_⟩
  have hT0 : 0≤T := by linarith
  have hTZ : T≤Z := by linarith
  have hX0 : 0<X := by linarith
  let w := X^(pairZeroHorizontalEnvelope Z)
  have hw : 0 ≤ w := Real.rpow_nonneg hX0.le _
  have hw2 : w^2 = X^(2*pairZeroHorizontalEnvelope Z) := pairZeroWeight_square _ _ hX0
  have hL : 0 ≤ Real.log (T+2) := Real.log_nonneg (by linarith)
  have hp (t : ℝ) (ht : t ∈ Set.Ioc 0 T) :
      ‖‖pairZeroCutoffVector X Z t‖^2-‖pairZeroWindowVector X T t‖^2‖ ≤
        K*w^2*Real.log (T+2)^2*pairZeroBoundaryProfile T t := by
    have hb : 0 ≤ pairZeroBoundaryProfile T t := by
      unfold pairZeroBoundaryProfile
      apply add_nonneg (div_nonneg (by norm_num) (by linarith [ht.1]))
      exact div_nonneg (by norm_num) (by linarith [ht.2])
    have hl : Real.log (|t|+2) ≤ Real.log (T+2) := by
      rw [abs_of_pos ht.1]
      exact Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2])
    have hg' : zeroKernelSum t ≤ G*Real.log (T+2) :=
      (hg t).2.trans (mul_le_mul_of_nonneg_left hl hG.le)
    have hu : ‖pairZeroCutoffVector X Z t‖ ≤ (4/3:ℝ)*w*G*Real.log (T+2) := by
      calc
        _ ≤ (4/3:ℝ)*w*zeroKernelSum t := pairZeroCutoff_envelope X Z t hX
        _ ≤ (4/3:ℝ)*w*(G*Real.log (T+2)) := mul_le_mul_of_nonneg_left hg' (by positivity)
        _ = _ := by ring
    have hv : ‖pairZeroWindowVector X T t‖ ≤ (4/3:ℝ)*w*G*Real.log (T+2) := by
      calc
        _ ≤ (4/3:ℝ)*w*zeroKernelSum t := pairZeroWindow_envelope X T Z t hX hT0 hTZ
        _ ≤ (4/3:ℝ)*w*(G*Real.log (T+2)) := mul_le_mul_of_nonneg_left hg' (by positivity)
        _ = _ := by ring
    have hr : ‖pairZeroCutoffVector X Z t-pairZeroWindowVector X T t‖ ≤
        (4/3:ℝ)*w*(D*Real.log (T+2)*pairZeroBoundaryProfile T t) :=
      (pairZeroHeightRemainder_majorant X T Z t hX hT0 hTZ).trans
        (mul_le_mul_of_nonneg_left (hd T t hT0 ht.1.le ht.2) (by positivity))
    rw [Real.norm_eq_abs]
    calc
      _ ≤ _ := pairZero_square_difference _ _
      _ ≤ ((4/3:ℝ)*w*(D*Real.log (T+2)*pairZeroBoundaryProfile T t))*
          ((4/3:ℝ)*w*G*Real.log (T+2)+(4/3:ℝ)*w*G*Real.log (T+2)) :=
        mul_le_mul hr (add_le_add hu hv) (by positivity) (by positivity)
      _ = _ := by dsimp [K]; ring
  have hi : IntervalIntegrable (fun t => K*w^2*Real.log (T+2)^2*pairZeroBoundaryProfile T t) volume 0 T :=
    (pairZeroBoundaryProfile_integrable T hT0).const_mul _
  have hb := intervalIntegral.norm_integral_le_of_norm_le hT0
    (Filter.Eventually.of_forall hp) hi
  rw [intervalIntegral.integral_const_mul,pairZeroBoundaryProfile_integral T hT0,
    Real.norm_eq_abs] at hb
  obtain ⟨hq,_,_,_,hlog⟩ := pairRHS_log_comparison T hT
  have hlog' : Real.log (1+T) ≤ 2*Real.log T :=
    (Real.log_le_log (by linarith : 0<1+T) (by linarith : 1+T ≤ T+2)).trans hlog
  have hprod : Real.log (T+2)^2*Real.log (1+T) ≤ 8*Real.log T^3 := by
    calc
      _ ≤ (2*Real.log T)^2*(2*Real.log T) :=
        mul_le_mul (sq_le_sq₀ hL (by linarith) |>.mpr hlog) hlog'
          (Real.log_nonneg (by linarith)) (sq_nonneg _)
      _ = _ := by ring
  unfold pairZeroHeightError
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
  calc
    _ ≤ 4*(K*w^2*Real.log (T+2)^2*(2*Real.log (1+T))) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = (8*K*w^2)*(Real.log (T+2)^2*Real.log (1+T)) := by ring
    _ ≤ (8*K*w^2)*(8*Real.log T^3) := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by rw [hw2]; ring

end
end HigherCorrelations
