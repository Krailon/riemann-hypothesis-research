import HigherCorrelations.PairRHSRemainderNorms
import HigherCorrelations.PairPrimeMeanEstimate

/-! UNCONDITIONAL exact signed square expansion. Every integral is over the same [0,T]. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem pairRHS_square_algebra (p a h : ℂ) :
    ‖-p+a+h‖^2 = ‖p‖^2+‖a‖^2+‖h‖^2-
      2*(p*star a).re-2*(p*star h).re+2*(a*star h).re := by
  simp [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re]
  ring

theorem pairRHS_integral_re (f : ℝ → ℂ) (T : ℝ)
    (hf : IntervalIntegrable f volume 0 T) :
    (∫ t in (0:ℝ)..T, (f t).re) = (∫ t in (0:ℝ)..T, f t).re :=
  Complex.reCLM.intervalIntegral_comp_comm hf

theorem pairRHS_square_integral (p a h : ℝ → ℂ) (T : ℝ)
    (hp : ContinuousOn p (Set.uIcc 0 T)) (ha : ContinuousOn a (Set.uIcc 0 T))
    (hh : ContinuousOn h (Set.uIcc 0 T)) :
    (∫ t in (0:ℝ)..T, ‖-p t+a t+h t‖^2) =
      (∫ t in (0:ℝ)..T, ‖p t‖^2)+(∫ t in (0:ℝ)..T, ‖a t‖^2)+
      (∫ t in (0:ℝ)..T, ‖h t‖^2)-2*(∫ t in (0:ℝ)..T, p t*star (a t)).re-
      2*(∫ t in (0:ℝ)..T, p t*star (h t)).re+2*(∫ t in (0:ℝ)..T, a t*star (h t)).re := by
  have hpa : ContinuousOn (fun t => p t*star (a t)) (Set.uIcc 0 T) := hp.mul ha.star
  have hph : ContinuousOn (fun t => p t*star (h t)) (Set.uIcc 0 T) := hp.mul hh.star
  have hah : ContinuousOn (fun t => a t*star (h t)) (Set.uIcc 0 T) := ha.mul hh.star
  have hp2 := hp.norm.pow 2
  have ha2 := ha.norm.pow 2
  have hh2 := hh.norm.pow 2
  have hpar := Complex.continuous_re.comp_continuousOn hpa
  have hphr := Complex.continuous_re.comp_continuousOn hph
  have hahr := Complex.continuous_re.comp_continuousOn hah
  simp_rw [pairRHS_square_algebra]
  simp (disch := (apply ContinuousOn.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add,intervalIntegral.integral_sub,intervalIntegral.integral_const_mul]
  rw [pairRHS_integral_re _ _ hpa.intervalIntegrable,
    pairRHS_integral_re _ _ hph.intervalIntegrable,pairRHS_integral_re _ _ hah.intervalIntegrable]

theorem pairRHS_cross_sum (f : ℝ → ℂ) (X T : ℝ) (hX : 1 ≤ X)
    (hf : ContinuousOn f (Set.uIcc 0 T)) :
    (∫ t in (0:ℝ)..T, f t*star (pairRHSRemainderSum X t)) =
      ∑ j, ∫ t in (0:ℝ)..T, f t*star (pairRHSRemainder j X t) := by
  simp only [pairRHSRemainderSum,star_sum,Finset.mul_sum]
  exact intervalIntegral.integral_finsetSum (fun j _ =>
    ((hf.mul (pairRHS_remainder_continuous j X hX).continuousOn.star).intervalIntegrable (μ := volume)))

theorem pairRHS_decomposition (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSSquare X T = T*Real.log T^2/X^2+T*Real.log X+
      pairRHSSmallError X T+pairRHSLargeError X T := by
  have hp := (pairRHS_prime_continuous X hX).continuousOn (s := Set.uIcc 0 T)
  have ha : ContinuousOn (pairRHSArch X) (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT]; exact pairRHSArch_continuous X T hT
  have hh : ContinuousOn (pairRHSRemainderSum X) (Set.uIcc 0 T) :=
    continuousOn_finsetSum _ (fun j _ => (pairRHS_remainder_continuous j X hX).continuousOn)
  have he := pairRHS_square_integral (fun t => pairPrimeSeries (X,t)) (pairRHSArch X)
    (pairRHSRemainderSum X) T hp ha hh
  rw [pairRHS_cross_sum _ X T hX hp,pairRHS_cross_sum _ X T hX ha] at he
  change pairRHSSquare X T = _ at he
  unfold pairRHSSmallError pairRHSLargeError pairRHSArchSquareError
    pairRHSPrimeArchError pairRHSPrimeError pairRHSArchError pairRHSRemainderSquare
    pairPrimeMeanDiagonalError pairPrimeMeanOffdiag pairPrimeMeanSquare
  rw [he]
  simp [Finset.univ,Fintype.elems]
  ring

end
end HigherCorrelations
