import HigherCorrelations.LittlewoodSegment

/-! UNCONDITIONAL. Compatible horizontal and vertical edge logarithms; zero-free boundaries. -/
namespace HigherCorrelations
noncomputable section
open Complex Set

theorem LittlewoodRectangle.horizontal {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (y : ℝ) (hy : y=c ∨ y=d)
    (x : ℝ) (hx : x ∈ Icc a b) :
    AnalyticAt ℂ f (x+y*I) ∧ f (x+y*I) ≠ 0 := by
  have hab := h.horizontal_lt.le
  have hcd := h.vertical_lt.le
  constructor
  · apply h.analytic
    rcases hy with rfl | rfl <;> simp [Rectangle, mem_reProdIm, uIcc_of_le, hab, hcd, hx]
  · apply h.nonzero
    rcases hy with rfl | rfl <;> simp [RectangleBorder, mem_reProdIm, uIcc_of_le, hab, hcd, hx]

theorem LittlewoodRectangle.vertical {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (x : ℝ) (hx : x=a ∨ x=b)
    (y : ℝ) (hy : y ∈ Icc c d) :
    AnalyticAt ℂ f (x+y*I) ∧ f (x+y*I) ≠ 0 := by
  have hab := h.horizontal_lt.le
  have hcd := h.vertical_lt.le
  constructor
  · apply h.analytic
    rcases hx with rfl | rfl <;> simp [Rectangle, mem_reProdIm, uIcc_of_le, hab, hcd, hy]
  · apply h.nonzero
    rcases hx with rfl | rfl <;> simp [RectangleBorder, mem_reProdIm, uIcc_of_le, hab, hcd, hy]

theorem littlewoodBottomLog_deriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (x : ℝ) (hx : x ∈ Icc a b) :
    HasDerivAt (littlewoodBottomLog f b c k) (logDeriv f (x+c*I)) x := by
  have hh := littlewoodSegmentLog_deriv f (c*I) 1 a b b x k
    ⟨h.horizontal_lt.le,le_rfl⟩ hx
    (fun x hx => by simpa [add_comm] using (h.horizontal c (Or.inl rfl) x hx).1)
    (fun x hx => by simpa [add_comm] using (h.horizontal c (Or.inl rfl) x hx).2)
  simpa [littlewoodBottomLog, add_comm] using hh

theorem littlewoodRightLog_deriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (t : ℝ) (ht : t ∈ Icc c d) :
    HasDerivAt (littlewoodRightLog f b c k) (I*logDeriv f (b+t*I)) t :=
  littlewoodSegmentLog_deriv f b I c d c t k ⟨le_rfl,h.vertical_lt.le⟩ ht
    (fun t ht => (h.vertical b (Or.inr rfl) t ht).1)
    (fun t ht => (h.vertical b (Or.inr rfl) t ht).2)

theorem littlewoodTopLog_deriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (x : ℝ) (hx : x ∈ Icc a b) :
    HasDerivAt (littlewoodTopLog f b c d k) (logDeriv f (x+d*I)) x := by
  have hh := littlewoodSegmentLog_deriv f (d*I) 1 a b b x
    (littlewoodRightLog f b c k d) ⟨h.horizontal_lt.le,le_rfl⟩ hx
    (fun x hx => by simpa [add_comm] using (h.horizontal d (Or.inr rfl) x hx).1)
    (fun x hx => by simpa [add_comm] using (h.horizontal d (Or.inr rfl) x hx).2)
  simpa [littlewoodTopLog, add_comm] using hh

theorem littlewoodBottomLog_exp {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (hk : exp k = f (b+c*I))
    (x : ℝ) (hx : x ∈ Icc a b) : exp (littlewoodBottomLog f b c k x) = f (x+c*I) := by
  simpa [littlewoodBottomLog, add_comm] using littlewoodSegmentLog_exp f (c*I) 1 a b b x k
    ⟨h.horizontal_lt.le,le_rfl⟩ hx
    (fun x hx => by simpa [add_comm] using (h.horizontal c (Or.inl rfl) x hx).1)
    (fun x hx => by simpa [add_comm] using (h.horizontal c (Or.inl rfl) x hx).2)
    (by simpa [add_comm] using hk)

theorem littlewoodRightLog_exp {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (hk : exp k = f (b+c*I))
    (t : ℝ) (ht : t ∈ Icc c d) : exp (littlewoodRightLog f b c k t) = f (b+t*I) :=
  littlewoodSegmentLog_exp f b I c d c t k ⟨le_rfl,h.vertical_lt.le⟩ ht
    (fun t ht => (h.vertical b (Or.inr rfl) t ht).1)
    (fun t ht => (h.vertical b (Or.inr rfl) t ht).2) hk

theorem littlewoodTopLog_exp {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (hk : exp k = f (b+c*I))
    (x : ℝ) (hx : x ∈ Icc a b) : exp (littlewoodTopLog f b c d k x) = f (x+d*I) := by
  simpa [littlewoodTopLog, add_comm] using littlewoodSegmentLog_exp f (d*I) 1 a b b x
    (littlewoodRightLog f b c k d) ⟨h.horizontal_lt.le,le_rfl⟩ hx
    (fun x hx => by simpa [add_comm] using (h.horizontal d (Or.inr rfl) x hx).1)
    (fun x hx => by simpa [add_comm] using (h.horizontal d (Or.inr rfl) x hx).2)
    (by simpa [add_comm] using littlewoodRightLog_exp h k hk d ⟨h.vertical_lt.le,le_rfl⟩)

theorem LittlewoodRectangle.horizontal_logDeriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (y : ℝ) (hy : y=c ∨ y=d) :
    ContinuousOn (fun x : ℝ => logDeriv f (x+y*I)) (Icc a b) := by
  intro x hx
  have hh := h.horizontal y hy x hx
  have hc : ContinuousAt (logDeriv f) (x+y*I) := hh.1.deriv.continuousAt.div hh.1.continuousAt hh.2
  exact (hc.comp (f := fun x : ℝ => (x:ℂ)+y*I) (by fun_prop)).continuousWithinAt

theorem LittlewoodRectangle.vertical_logDeriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (x : ℝ) (hx : x=a ∨ x=b) :
    ContinuousOn (fun t : ℝ => I*logDeriv f (x+t*I)) (Icc c d) := by
  intro t ht
  have hh := h.vertical x hx t ht
  have hc : ContinuousAt (logDeriv f) (x+t*I) := hh.1.deriv.continuousAt.div hh.1.continuousAt hh.2
  exact ((hc.comp (f := fun t : ℝ => (x:ℂ)+t*I) (by fun_prop)).const_mul I).continuousWithinAt

theorem littlewoodLog_re_of_exp {w y : ℂ} (h : exp w = y) : w.re = Real.log ‖y‖ := by
  rw [← h, norm_exp, Real.log_exp]

theorem littlewood_vertical_log_integrable {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (x : ℝ) (hx : x=a ∨ x=b) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖f (x+t*I)‖)
      MeasureTheory.volume c d := by
  apply ContinuousOn.intervalIntegrable_of_Icc h.vertical_lt.le
  intro t ht
  have hh := h.vertical x hx t ht
  have hp : ContinuousAt (fun t : ℝ => (x:ℂ)+t*I) t := by fun_prop
  exact (((hh.1.continuousAt.comp (f := fun t : ℝ => (x:ℂ)+t*I) hp).norm).log
    (norm_ne_zero_iff.mpr hh.2)).continuousWithinAt

theorem littlewood_arguments_integrable {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) :
    IntervalIntegrable (fun x => (littlewoodTopLog f b c d k x).im -
      (littlewoodBottomLog f b c k x).im) MeasureTheory.volume a b := by
  have ht : ContinuousOn (littlewoodTopLog f b c d k) (Icc a b) :=
    fun x hx => (littlewoodTopLog_deriv h k x hx).continuousAt.continuousWithinAt
  have hb : ContinuousOn (littlewoodBottomLog f b c k) (Icc a b) :=
    fun x hx => (littlewoodBottomLog_deriv h k x hx).continuousAt.continuousWithinAt
  exact ((Complex.continuous_im.comp_continuousOn ht).sub
    (Complex.continuous_im.comp_continuousOn hb)).intervalIntegrable_of_Icc h.horizontal_lt.le

end
end HigherCorrelations
