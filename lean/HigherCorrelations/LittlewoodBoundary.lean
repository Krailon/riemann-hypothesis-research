import HigherCorrelations.LittlewoodEdges

/-! UNCONDITIONAL. Exact boundary identity with compatible arguments and verified integrability. -/
namespace HigherCorrelations
noncomputable section
open Complex Set MeasureTheory

theorem littlewood_boundary_integral {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (hk : exp k = f (b+c*I)) :
    (RectangleIntegral (fun s => (s-(a+c*I))*logDeriv f s) (a+c*I) (b+d*I)).im =
      littlewoodBoundary f a b c d k := by
  let B := littlewoodBottomLog f b c k
  let R := littlewoodRightLog f b c k
  let U := littlewoodTopLog f b c d k
  let L := littlewoodSegmentLog f a I c (B a)
  have hab := h.horizontal_lt.le
  have hcd := h.vertical_lt.le
  have hB := littlewoodBottomLog_deriv h k
  have hR := littlewoodRightLog_deriv h k
  have hU := littlewoodTopLog_deriv h k
  have hL : ∀ t ∈ Icc c d, HasDerivAt L (I*logDeriv f (a+t*I)) t := by
    intro t ht
    exact littlewoodSegmentLog_deriv f a I c d c t (B a) ⟨le_rfl,hcd⟩ ht
      (fun t ht => (h.vertical a (Or.inl rfl) t ht).1)
      (fun t ht => (h.vertical a (Or.inl rfl) t ht).2)
  have heL : ∀ t ∈ Icc c d, exp (L t) = f (a+t*I) := by
    intro t ht
    exact littlewoodSegmentLog_exp f a I c d c t (B a) ⟨le_rfl,hcd⟩ ht
      (fun t ht => (h.vertical a (Or.inl rfl) t ht).1)
      (fun t ht => (h.vertical a (Or.inl rfl) t ht).2)
      (littlewoodBottomLog_exp h k hk a ⟨le_rfl,hab⟩)
  have hcB : ContinuousOn B (Icc a b) := fun x hx => (hB x hx).continuousAt.continuousWithinAt
  have hcU : ContinuousOn U (Icc a b) := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  have hcR : ContinuousOn R (Icc c d) := fun x hx => (hR x hx).continuousAt.continuousWithinAt
  have hcL : ContinuousOn L (Icc c d) := fun x hx => (hL x hx).continuousAt.continuousWithinAt
  have hiB : IntervalIntegrable B volume a b := hcB.intervalIntegrable_of_Icc hab
  have hiU : IntervalIntegrable U volume a b := hcU.intervalIntegrable_of_Icc hab
  have hiR : IntervalIntegrable R volume c d := hcR.intervalIntegrable_of_Icc hcd
  have hiL : IntervalIntegrable L volume c d := hcL.intervalIntegrable_of_Icc hcd
  have iB := littlewood_affine_integral B (fun x => logDeriv f (x+c*I)) a b (-a) 1 hab hB
    (h.horizontal_logDeriv c (Or.inl rfl))
  have iU := littlewood_affine_integral U (fun x => logDeriv f (x+d*I)) a b
    (-a+(d-c)*I) 1 hab hU (h.horizontal_logDeriv d (Or.inr rfl))
  have iR := littlewood_affine_integral R (fun t => I*logDeriv f (b+t*I)) c d
    (b-a-c*I) I hcd hR (h.vertical_logDeriv b (Or.inr rfl))
  have iL := littlewood_affine_integral L (fun t => I*logDeriv f (a+t*I)) c d
    (-c*I) I hcd hL (h.vertical_logDeriv a (Or.inl rfl))
  have hcorners : B b = k ∧ R c = k ∧ U b = R d := by
    simp [B,R,U,littlewoodBottomLog,littlewoodRightLog,littlewoodTopLog,littlewoodSegmentLog]
  have hcontour : RectangleIntegral (fun s => (s-(a+c*I))*logDeriv f s) (a+c*I) (b+d*I) =
      I*(d-c)*(U a-L d) + (∫ x in a..b, U x) - (∫ x in a..b, B x) +
      I*((∫ t in c..d, L t)-(∫ t in c..d, R t)) := by
    unfold RectangleIntegral HIntegral VIntegral
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_zero, add_zero, add_im, mul_im, mul_one, zero_add, smul_eq_mul]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    have eB : (fun x : ℝ => (x+c*I-(a+c*I))*logDeriv f (x+c*I)) =
        (fun x : ℝ => (-a+x*1)*logDeriv f (x+c*I)) := by ext x; ring
    have eU : (fun x : ℝ => (x+d*I-(a+c*I))*logDeriv f (x+d*I)) =
        (fun x : ℝ => (-a+(d-c)*I+x*1)*logDeriv f (x+d*I)) := by ext x; ring
    have eR : (fun t : ℝ => I*((b+t*I-(a+c*I))*logDeriv f (b+t*I))) =
        (fun t : ℝ => (b-a-c*I+t*I)*(I*logDeriv f (b+t*I))) := by ext t; ring
    have eL : (fun t : ℝ => I*((a+t*I-(a+c*I))*logDeriv f (a+t*I))) =
        (fun t : ℝ => (-c*I+t*I)*(I*logDeriv f (a+t*I))) := by ext t; ring
    rw [eB,eU,eR,eL,iB,iU,iR,iL,hcorners.1,hcorners.2.1,hcorners.2.2]
    ring
  have hcornerRe : (U a).re = (L d).re := by
    rw [littlewoodLog_re_of_exp (littlewoodTopLog_exp h k hk a ⟨le_rfl,hab⟩),
      littlewoodLog_re_of_exp (heL d ⟨hcd,le_rfl⟩)]
  have hleft : (∫ t in c..d, L t).re = ∫ t in c..d, Real.log ‖f (a+t*I)‖ := by
    rw [littlewood_integral_re L c d hiL]
    apply intervalIntegral.integral_congr
    intro t ht
    exact littlewoodLog_re_of_exp (heL t (by simpa [uIcc_of_le hcd] using ht))
  have hright : (∫ t in c..d, R t).re = ∫ t in c..d, Real.log ‖f (b+t*I)‖ := by
    rw [littlewood_integral_re R c d hiR]
    apply intervalIntegral.integral_congr
    intro t ht
    exact littlewoodLog_re_of_exp (littlewoodRightLog_exp h k hk t (by simpa [uIcc_of_le hcd] using ht))
  have hargs : (∫ x in a..b, U x).im-(∫ x in a..b, B x).im =
      ∫ x in a..b, (U x).im-(B x).im := by
    have hu : IntervalIntegrable (fun x => (U x).im) volume a b :=
      (Complex.continuous_im.comp_continuousOn hcU).intervalIntegrable_of_Icc hab
    have hb : IntervalIntegrable (fun x => (B x).im) volume a b :=
      (Complex.continuous_im.comp_continuousOn hcB).intervalIntegrable_of_Icc hab
    rw [littlewood_integral_im U a b hiU, littlewood_integral_im B a b hiB]
    exact (intervalIntegral.integral_sub hu hb).symm
  rw [hcontour]
  simp only [add_im, sub_im, sub_re, mul_im, mul_re, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, zero_add, mul_zero, sub_zero, hcornerRe, sub_self, hleft, hright]
  change _ = _ - _ + (∫ x in a..b, (U x).im-(B x).im)
  rw [← hargs]
  ring

end
end HigherCorrelations
