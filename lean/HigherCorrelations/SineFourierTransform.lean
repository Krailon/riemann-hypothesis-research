import HigherCorrelations.SineParameterIntegral

/-! UNCONDITIONAL inverse transform of the compact hexagonal density. -/
namespace HigherCorrelations
noncomputable section
open Set MeasureTheory
open scoped FourierTransform SchwartzMap

theorem sineInterval_character (u : ℝ) :
    (∫ a : ℝ, pairMeanBox a * pairMeanCharacter (u*a)) = (pairMeanSinc u : ℂ) := by
  have he : (fun a : ℝ => pairMeanBox a*pairMeanCharacter (u*a)) =
      (fun a : ℝ => pairMeanCharacter (-a*(-u))*pairMeanBox a) := by
    funext a
    rw [show -a*(-u) = u*a by ring,mul_comm]
  rw [he]
  change pairMeanFourier pairMeanBox (-u) = _
  rw [pairMeanBox_fourier,pairMeanSinc_even]

theorem sineParameterIntegrand_plane_integral (u v d : ℝ) :
    (∫ p : ℝ × ℝ, sineParameterIntegrand u v (d,p)) =
      pairMeanBox d*pairMeanCharacter ((u-v)*d)*(pairMeanSinc u:ℂ)*(pairMeanSinc v:ℂ) := by
  rw [← integral_add_right_eq_self (fun p : ℝ × ℝ => sineParameterIntegrand u v (d,p)) (d,-d)]
  have he (p : ℝ × ℝ) : sineParameterIntegrand u v (d,p+(d,-d)) =
      (pairMeanBox d*pairMeanCharacter ((u-v)*d)) *
        ((pairMeanBox p.1*pairMeanCharacter (u*p.1)) *
         (pairMeanBox p.2*pairMeanCharacter (v*p.2))) := by
    simp only [sineParameterIntegrand,Prod.fst_add,Prod.snd_add,
      add_sub_cancel_right,neg_add_cancel_right]
    rw [show u*(p.1+d)+v*(p.2+-d) = (u-v)*d+(u*p.1+v*p.2) by ring,
      pairMeanCharacter_add,pairMeanCharacter_add]
    ring
  simp_rw [he]
  rw [integral_const_mul,Measure.volume_eq_prod,integral_prod_mul (fun a : ℝ => pairMeanBox a*pairMeanCharacter (u*a))
    (fun b : ℝ => pairMeanBox b*pairMeanCharacter (v*b)),
    sineInterval_character,sineInterval_character]
  ring

theorem sineCycleDensity_inverse_integral (u v : ℝ) :
    (∫ p : ℝ × ℝ, (sineCycleDensity p.1 p.2:ℂ)*pairMeanCharacter (u*p.1+v*p.2)) =
      sineCycle (u,v) := by
  simp_rw [← sineParameterIntegrand_inner u v]
  rw [sineParameterIntegrand_fubini]
  simp_rw [sineParameterIntegrand_plane_integral]
  rw [integral_mul_const,integral_mul_const,sineInterval_character]
  simp only [sineCycle]
  ring

theorem sineDensityPlane_inverse (x : FourierPlane) :
    (𝓕⁻ sineDensityPlane) x = sineCyclePlane x := by
  have h := complexFourier_real_eq_inverse
    (fun p : ℝ × ℝ => (sineCycleDensity p.1 p.2:ℂ)) (planeCoords x)
  have he : complexFourier (fun p : ℝ × ℝ => (sineCycleDensity p.1 p.2:ℂ))
      (((planeCoords x).1:ℂ),((planeCoords x).2:ℂ)) = sineCyclePlane x := by
    rw [complexFourier]
    convert sineCycleDensity_inverse_integral (planeCoords x).1 (planeCoords x).2 using 1
    congr 1
    funext p
    simp only [pairMeanCharacter,Complex.ofReal_add,Complex.ofReal_mul]
    congr 2
  rw [h] at he
  exact he

theorem sineDensityPlane_fourier (x : FourierPlane) :
    (𝓕 sineDensityPlane) x = sineCyclePlane x := by
  have h := sineDensityPlane_inverse (-x)
  rw [Real.fourierInv_eq_fourier_neg,neg_neg] at h
  simpa only [sineCyclePlane,map_neg,sineCycle_reflection] using h

theorem sineDensityPlane_mass : (∫ x : FourierPlane, sineDensityPlane x) = 1 := by
  have h := sineDensityPlane_fourier 0
  simpa [Real.fourier_eq,sineCyclePlane,sineCycle,pairMeanSinc_zero] using h

end
end HigherCorrelations
