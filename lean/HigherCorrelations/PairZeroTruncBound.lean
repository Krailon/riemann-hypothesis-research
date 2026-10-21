import HigherCorrelations.PairZeroMajorants
import HigherCorrelations.PairRHSArchIntegrals

/-! UNCONDITIONAL truncation bound, retaining the quadratic remainder and the
endpoint Z = 2T. Constants are absolute existential constants. -/
namespace HigherCorrelations
noncomputable section

theorem pairZero_square_difference (u v : ℂ) :
    |‖u‖^2-‖v‖^2| ≤ ‖u-v‖*(‖u‖+‖v‖) := by
  rw [show ‖u‖^2-‖v‖^2 = (‖u‖-‖v‖)*(‖u‖+‖v‖) by ring,abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v) (by positivity)

theorem pairZero_square_trunc (u v : ℂ) (A R : ℝ)
    (hu : ‖u‖ ≤ A) (hr : ‖u-v‖ ≤ R) :
    |‖u‖^2-‖v‖^2| ≤ 2*A*R+R^2 := by
  have hA : 0 ≤ A := (norm_nonneg _).trans hu
  have hR : 0 ≤ R := (norm_nonneg _).trans hr
  have hv : ‖v‖ ≤ A+R := by
    calc
      _ = ‖u-(u-v)‖ := by congr 1; abel
      _ ≤ ‖u‖+‖u-v‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hu hr
  calc
    _ ≤ ‖u-v‖*(‖u‖+‖v‖) := pairZero_square_difference u v
    _ ≤ R*(A+(A+R)) := mul_le_mul hr (add_le_add hu hv) (by positivity) hR
    _ = _ := by ring

theorem pairZeroTruncError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
      |pairZeroTruncError X T Z| ≤ C*X*T*
        (Real.log (T+2)*Real.log Z/Z + Real.log Z^2/Z^2) := by
  obtain ⟨G,hG,hg⟩ := zeroKernel_summable_bound
  obtain ⟨D,hD,hd⟩ := zeroKernel_distant_bound
  let A := (4/3:ℝ)*G
  let B := (4/3:ℝ)*D
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨4*(2*A*B+B^2),by positivity,fun X T Z hX hT hZ => ?_⟩
  have hX0 : 0<X := by linarith
  have hZ0 : 0<Z := by linarith
  have hT0 : 0≤T := by linarith
  have hL : 0≤Real.log (T+2) := Real.log_nonneg (by linarith)
  have hq : 0≤Real.log Z/Z := div_nonneg (Real.log_nonneg (by linarith)) hZ0.le
  have hs : (X^((1:ℝ)/2))^2 = X := by
    rw [pairZeroWeight_square X (1/2) hX0]
    norm_num
  have hp (t : ℝ) (ht : t ∈ Set.uIoc 0 T) :
      ‖‖pairZeroFullVector X t‖^2-‖pairZeroCutoffVector X Z t‖^2‖ ≤
        (2*A*B+B^2)*X*(Real.log (T+2)*Real.log Z/Z+Real.log Z^2/Z^2) := by
    rw [Set.uIoc_of_le hT0] at ht
    have hu : ‖pairZeroFullVector X t‖ ≤ A*X^((1:ℝ)/2)*Real.log (T+2) := by
      have hl : Real.log (|t|+2) ≤ Real.log (T+2) := by
        rw [abs_of_pos ht.1]
        exact Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2])
      calc
        _ ≤ (4/3:ℝ)*X^((1:ℝ)/2)*zeroKernelSum t := pairZeroFull_majorant X t hX
        _ ≤ (4/3:ℝ)*X^((1:ℝ)/2)*(G*Real.log (T+2)) :=
          mul_le_mul_of_nonneg_left ((hg t).2.trans (mul_le_mul_of_nonneg_left hl hG.le)) (by positivity)
        _ = _ := by dsimp [A]; ring
    have hr : ‖pairZeroFullVector X t-pairZeroCutoffVector X Z t‖ ≤
        B*X^((1:ℝ)/2)*(Real.log Z/Z) := by
      calc
        _ ≤ _ := pairZeroRemainder_majorant X Z t hX
        _ ≤ (4/3:ℝ)*X^((1:ℝ)/2)*(D*Real.log Z/Z) :=
          mul_le_mul_of_nonneg_left (hd T Z t hT hZ ht.1.le ht.2) (by positivity)
        _ = _ := by dsimp [B]; ring
    rw [Real.norm_eq_abs]
    apply (pairZero_square_trunc _ _ _ _ hu hr).trans
    have he : 2*(A*X^((1:ℝ)/2)*Real.log (T+2))*(B*X^((1:ℝ)/2)*(Real.log Z/Z))+
        (B*X^((1:ℝ)/2)*(Real.log Z/Z))^2 =
        X*(2*A*B*(Real.log (T+2)*(Real.log Z/Z))+B^2*(Real.log Z/Z)^2) := by
      calc
        _ = (X^((1:ℝ)/2))^2*(2*A*B*(Real.log (T+2)*(Real.log Z/Z))+B^2*(Real.log Z/Z)^2) := by ring
        _ = _ := by rw [hs]
    rw [he]
    have hp₁ : 0 ≤ B^2*(Real.log (T+2)*(Real.log Z/Z)) := by positivity
    have hp₂ : 0 ≤ 2*A*B*(Real.log Z/Z)^2 := by positivity
    have eq : Real.log Z^2/Z^2 = (Real.log Z/Z)^2 := (div_pow _ _ _).symm
    rw [eq]
    apply sub_nonneg.mp
    convert mul_nonneg hX0.le (add_nonneg hp₁ hp₂) using 1 <;> ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hp
  rw [Real.norm_eq_abs,sub_zero,abs_of_nonneg hT0] at hb
  unfold pairZeroTruncError
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
  calc
    _ ≤ 4*((2*A*B+B^2)*X*(Real.log (T+2)*Real.log Z/Z+Real.log Z^2/Z^2)*T) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end
end HigherCorrelations
