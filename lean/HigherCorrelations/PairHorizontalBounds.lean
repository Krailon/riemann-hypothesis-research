import HigherCorrelations.PairHadamardBounds
import HigherCorrelations.PairZetaLogDerivative
import HigherCorrelations.PairDigammaBounds
import HigherCorrelations.PairContourAlgebra

/-! Horizontal contour majorants from an audited Hadamard expansion.
UNCONDITIONAL. The coarser R^(3/2)/ε bound suffices with ε of order 1/log R;
this file does not assert the sharper classical O(log² R) bound. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem pairZeta_horizontal_majorant (M : ℕ) :
    ∃ D r A B Q G : ℝ, 0 ≤ D ∧ 0 < r ∧ 0 < A ∧ 0 ≤ B ∧ 0 ≤ Q ∧ 0 < G ∧
      ∀ (σ v R ε : ℝ), -(2*M+1) ≤ σ → σ ≤ 5/2 → 2 ≤ |v| →
        1 ≤ R → ‖(σ:ℂ)+(v:ℂ)*I‖ ≤ R → 0 < ε →
        (∀ i : ZeroOccurrence, ε ≤ |v-occurrenceOrdinate i|) →
        ‖-deriv riemannZeta ((σ:ℂ)+(v:ℂ)*I) / riemannZeta ((σ:ℂ)+(v:ℂ)*I)‖ ≤
          D + ((A*(1+4*R)^(3/2:ℝ)+B)/Real.log 2)*(1/ε+1/r) + 2*R*Q +
            1 + |Real.log Real.pi|/2 + G*Real.log (|v|+2)/2 := by
  obtain ⟨D,r,A,B,Q,hD,hr,hA,hB,hQ,hxi⟩ := pairXi_logDeriv_bound
  obtain ⟨G,hG,hgamma⟩ := pairDigamma_horizontal_bound M
  refine ⟨D,r,A,B,Q,G,hD,hr,hA,hB,hQ,hG,fun σ v R ε hlo hhi hv hR hz hε hgap => ?_⟩
  let z : ℂ := (σ:ℂ)+(v:ℂ)*I
  have hv0 : v ≠ 0 := by intro he; norm_num [he] at hv
  have hz0 : z.im ≠ 0 := by simpa [z] using hv0
  have hζ := pairGoodHeight_zeta_ne_zero v ε hv0 hε hgap σ
  change ‖-deriv riemannZeta z / riemannZeta z‖ ≤ _
  rw [pairZeta_logDeriv_xi z hz0 hζ]
  have hxb := hxi z R ε hR hz hε (by simpa [z] using hgap)
  have hgb := hgamma σ v hlo hhi hv
  have hp : ‖1/(z-1)‖ ≤ 1 := by
    have hh : 1 ≤ ‖z-1‖ := by
      have him := Complex.abs_im_le_norm (z-1)
      simp [z] at him
      linarith
    simpa only [norm_div, norm_one, div_le_one (by linarith : 0 < ‖z-1‖)] using hh
  have hn := norm_add_le (-logDeriv riemannXi z + 1/(z-1) - (1/2:ℂ)*(Real.log Real.pi:ℂ))
    ((1/2:ℂ)*digamma (z/2+1))
  have hn' := norm_sub_le (-logDeriv riemannXi z + 1/(z-1)) ((1/2:ℂ)*(Real.log Real.pi:ℂ))
  have hn'' := norm_add_le (-logDeriv riemannXi z) (1/(z-1))
  norm_num only [norm_neg, norm_mul, norm_div, norm_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs] at hn hn' hn'' hp
  change ‖digamma (z/2+1)‖ ≤ _ at hgb
  linarith

theorem pairContourKernel_horizontal_bound (X t σ v : ℝ) (hX : 1 ≤ X)
    (hσ : σ ≤ 5/2) (hv : v-t ≠ 0) :
    ‖pairContourKernel X t ((σ:ℂ)+(v:ℂ)*I)‖ ≤ 2*X^2/(v-t)^2 := by
  have hX0 : 0 < X := by linarith
  have he : ‖Complex.exp ((Real.log X:ℂ)*((σ:ℂ)+(v:ℂ)*I-pairSpectralPoint t))‖ ≤ X^2 := by
    rw [Complex.norm_exp]
    have hre : ((Real.log X:ℂ)*((σ:ℂ)+(v:ℂ)*I-pairSpectralPoint t)).re =
        Real.log X*(σ-1/2) := by simp [pairSpectralPoint, Complex.mul_re]
    rw [hre]
    calc
      _ ≤ Real.exp (Real.log X*2) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (by linarith) (Real.log_nonneg hX))
      _ = X^2 := by rw [show Real.log X*2 = Real.log X+Real.log X by ring,
        Real.exp_add, Real.exp_log hX0]; ring
  have hd : (v-t)^2 ≤ ‖(((σ:ℂ)+(v:ℂ)*I)-pairSpectralPoint t)^2-1‖ := by
    rw [pairContourKernel_denominator_factor, norm_mul]
    have h₁ : |v-t| ≤ ‖((σ:ℂ)+(v:ℂ)*I)-(pairSpectralPoint t+1)‖ := by
      simpa [pairSpectralPoint] using Complex.abs_im_le_norm
        (((σ:ℂ)+(v:ℂ)*I)-(pairSpectralPoint t+1))
    have h₂ : |v-t| ≤ ‖((σ:ℂ)+(v:ℂ)*I)-(pairSpectralPoint t-1)‖ := by
      simpa [pairSpectralPoint] using Complex.abs_im_le_norm
        (((σ:ℂ)+(v:ℂ)*I)-(pairSpectralPoint t-1))
    simpa [← pow_two, sq_abs] using mul_le_mul h₁ h₂ (abs_nonneg _) (norm_nonneg _)
  unfold pairContourKernel
  rw [norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left he (by norm_num))
    (sq_pos_of_ne_zero hv) hd

end
end HigherCorrelations
