import HigherCorrelations.LittlewoodDefinitions

-- Expected statements only; unfinished bodies must be rejected.
namespace HigherCorrelations
noncomputable section
open Complex Set MeasureTheory
open scoped Classical

theorem littlewoodSegmentLog_start (f : ℂ → ℂ) (z v : ℂ) (t₀ : ℝ) (k : ℂ) :
    littlewoodSegmentLog f z v t₀ k t₀ = k := by sorry

theorem littlewoodSegmentLog_deriv (f : ℂ → ℂ) (z v : ℂ) (a b t₀ t : ℝ) (k : ℂ)
    (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, AnalyticAt ℂ f (z+x*v))
    (hn : ∀ x ∈ Icc a b, f (z+x*v) ≠ 0) :
    HasDerivAt (littlewoodSegmentLog f z v t₀ k) (v * logDeriv f (z+t*v)) t := by sorry

theorem littlewoodSegmentLog_exp (f : ℂ → ℂ) (z v : ℂ) (a b t₀ t : ℝ) (k : ℂ)
    (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, AnalyticAt ℂ f (z+x*v))
    (hn : ∀ x ∈ Icc a b, f (z+x*v) ≠ 0) (hk : exp k = f (z+t₀*v)) :
    exp (littlewoodSegmentLog f z v t₀ k t) = f (z+t*v) := by sorry

theorem littlewoodSegmentLog_re (f : ℂ → ℂ) (z v : ℂ) (a b t₀ t : ℝ) (k : ℂ)
    (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, AnalyticAt ℂ f (z+x*v))
    (hn : ∀ x ∈ Icc a b, f (z+x*v) ≠ 0) (hk : exp k = f (z+t₀*v)) :
    (littlewoodSegmentLog f z v t₀ k t).re = Real.log ‖f (z+t*v)‖ := by sorry

theorem littlewood_affine_integral (L Q : ℝ → ℂ) (a b : ℝ) (w₀ w₁ : ℂ)
    (hab : a ≤ b) (hL : ∀ x ∈ Icc a b, HasDerivAt L (Q x) x)
    (hQ : ContinuousOn Q (Icc a b)) :
    (∫ x in a..b, (w₀+x*w₁)*Q x) =
      (w₀+b*w₁)*L b-(w₀+a*w₁)*L a-w₁*(∫ x in a..b, L x) := by sorry

theorem littlewood_integral_re (F : ℝ → ℂ) (a b : ℝ) (hF : IntervalIntegrable F volume a b) :
    (∫ x in a..b, F x).re = ∫ x in a..b, (F x).re := by sorry

theorem littlewood_integral_im (F : ℝ → ℂ) (a b : ℝ) (hF : IntervalIntegrable F volume a b) :
    (∫ x in a..b, F x).im = ∫ x in a..b, (F x).im := by sorry

theorem LittlewoodRectangle.horizontal {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (y : ℝ) (hy : y=c ∨ y=d)
    (x : ℝ) (hx : x ∈ Icc a b) :
    AnalyticAt ℂ f (x+y*I) ∧ f (x+y*I) ≠ 0 := by sorry

theorem LittlewoodRectangle.vertical {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (x : ℝ) (hx : x=a ∨ x=b)
    (y : ℝ) (hy : y ∈ Icc c d) :
    AnalyticAt ℂ f (x+y*I) ∧ f (x+y*I) ≠ 0 := by sorry

theorem littlewoodBottomLog_deriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (x : ℝ) (hx : x ∈ Icc a b) :
    HasDerivAt (littlewoodBottomLog f b c k) (logDeriv f (x+c*I)) x := by sorry

theorem littlewoodRightLog_deriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (t : ℝ) (ht : t ∈ Icc c d) :
    HasDerivAt (littlewoodRightLog f b c k) (I*logDeriv f (b+t*I)) t := by sorry

theorem littlewoodTopLog_deriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (x : ℝ) (hx : x ∈ Icc a b) :
    HasDerivAt (littlewoodTopLog f b c d k) (logDeriv f (x+d*I)) x := by sorry

theorem littlewoodBottomLog_exp {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (hk : exp k = f (b+c*I))
    (x : ℝ) (hx : x ∈ Icc a b) : exp (littlewoodBottomLog f b c k x) = f (x+c*I) := by sorry

theorem littlewoodRightLog_exp {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (hk : exp k = f (b+c*I))
    (t : ℝ) (ht : t ∈ Icc c d) : exp (littlewoodRightLog f b c k t) = f (b+t*I) := by sorry

theorem littlewoodTopLog_exp {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (hk : exp k = f (b+c*I))
    (x : ℝ) (hx : x ∈ Icc a b) : exp (littlewoodTopLog f b c d k x) = f (x+d*I) := by sorry

theorem LittlewoodRectangle.horizontal_logDeriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (y : ℝ) (hy : y=c ∨ y=d) :
    ContinuousOn (fun x : ℝ => logDeriv f (x+y*I)) (Icc a b) := by sorry

theorem LittlewoodRectangle.vertical_logDeriv {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (x : ℝ) (hx : x=a ∨ x=b) :
    ContinuousOn (fun t : ℝ => I*logDeriv f (x+t*I)) (Icc c d) := by sorry

theorem littlewoodLog_re_of_exp {w y : ℂ} (h : exp w = y) : w.re = Real.log ‖y‖ := by sorry

theorem littlewood_vertical_log_integrable {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (x : ℝ) (hx : x=a ∨ x=b) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖f (x+t*I)‖)
      MeasureTheory.volume c d := by sorry

theorem littlewood_arguments_integrable {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) :
    IntervalIntegrable (fun x => (littlewoodTopLog f b c d k x).im -
      (littlewoodBottomLog f b c k x).im) MeasureTheory.volume a b := by sorry

theorem littlewood_boundary_integral {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k : ℂ) (hk : exp k = f (b+c*I)) :
    (RectangleIntegral (fun s => (s-(a+c*I))*logDeriv f s) (a+c*I) (b+d*I)).im =
      littlewoodBoundary f a b c d k := by sorry

theorem littlewood_zero_set_exists {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) :
    ∃ Z : Finset ℂ, ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0 := by sorry

theorem littlewood_weighted_argument {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0) :
    (RectangleIntegral (fun s => (s-(a+c*I))*logDeriv f s) (a+c*I) (b+d*I)).im =
      2*Real.pi*littlewoodMass f Z a := by sorry

theorem littlewood_identity {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0)
    (k : ℂ) (hk : exp k = f (b+c*I)) :
    2*Real.pi*littlewoodMass f Z a = littlewoodBoundary f a b c d k := by sorry

theorem littlewood_mass_count (f : ℂ → ℂ) (Z : Finset ℂ) (a σ : ℝ)
    (hσ : a < σ) (hZ : ∀ s ∈ Z, a ≤ s.re) :
    (σ-a)*(littlewoodRightCount f Z σ : ℝ) ≤ littlewoodMass f Z a := by sorry

theorem littlewood_count_bound {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0)
    (k : ℂ) (hk : exp k = f (b+c*I)) (σ : ℝ) (hσ : a < σ) :
    (littlewoodRightCount f Z σ : ℝ) ≤ littlewoodBoundary f a b c d k / (2*Real.pi*(σ-a)) := by sorry

theorem littlewood_count_of_budget {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0)
    (k : ℂ) (hk : exp k = f (b+c*I)) (σ E : ℝ) (hσ : a < σ)
    (hE : littlewoodBoundary f a b c d k ≤ E) :
    (littlewoodRightCount f Z σ : ℝ) ≤ E / (2*Real.pi*(σ-a)) := by sorry

theorem littlewood_boundary_branch_invariant {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k l : ℂ)
    (hk : exp k = f (b+c*I)) (hl : exp l = f (b+c*I)) :
    littlewoodBoundary f a b c d k = littlewoodBoundary f a b c d l := by sorry

theorem littlewood_count_threshold (f : ℂ → ℂ) (Z : Finset ℂ) (σ : ℝ)
    (hZ : ∀ s ∈ Z, s.re = σ) : littlewoodRightCount f Z σ = 0 := by sorry

theorem littlewood_zeta_count {a σ c d : ℝ}
    (h : LittlewoodRectangle riemannZeta a 2 c d) (ha : 0 < a) (hσ : a < σ)
    (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (2+d*I) ∧ riemannZeta s = 0) :
    littlewoodRightCount riemannZeta Z σ = (rightDensityWindow c d (σ-1/2)).card := by sorry

theorem littlewood_zeta_bound {a σ c d : ℝ}
    (h : LittlewoodRectangle riemannZeta a 2 c d) (ha : 0 < a) (hσ : a < σ)
    (k : ℂ) (hk : exp k = riemannZeta (2+c*I)) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤
      littlewoodBoundary riemannZeta a 2 c d k / (2*Real.pi*(σ-a)) := by sorry

theorem littlewood_zeta_of_budget {a σ c d E : ℝ}
    (h : LittlewoodRectangle riemannZeta a 2 c d) (ha : 0 < a) (hσ : a < σ)
    (k : ℂ) (hk : exp k = riemannZeta (2+c*I))
    (hE : littlewoodBoundary riemannZeta a 2 c d k ≤ E) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤ E / (2*Real.pi*(σ-a)) := by sorry

theorem littlewood_zeta_rectangle (a c d : ℝ) (ha : a < 2) (hc : 0 < c) (hcd : c < d)
    (hn : ∀ s ∈ RectangleBorder (a+c*I) (2+d*I), riemannZeta s ≠ 0) :
    LittlewoodRectangle riemannZeta a 2 c d := by sorry

theorem littlewood_zeta_budget_positive_height (a σ c d E : ℝ)
    (ha : 0 < a) (hσ : a < σ) (hσ' : σ < 1) (hc : 0 < c) (hcd : c < d)
    (hn : ∀ s ∈ RectangleBorder (a+c*I) (2+d*I), riemannZeta s ≠ 0)
    (hE : littlewoodBoundary riemannZeta a 2 c d (Complex.log (riemannZeta (2+c*I))) ≤ E) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤ E / (2*Real.pi*(σ-a)) := by sorry

theorem littlewood_constant_boundary (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (w : ℂ) (hw : w ≠ 0) (k : ℂ) (hk : exp k = w) :
    littlewoodBoundary (fun _ => w) a b c d k = 0 := by sorry

theorem littlewood_repeated_zero (a b c d : ℝ) (ρ : ℂ) (m : ℕ) (hm : 0 < m)
    (ha : a < ρ.re) (hb : ρ.re < b) (hc : c < ρ.im) (hd : ρ.im < d)
    (k : ℂ) (hk : exp k = (b+c*I-ρ)^m) :
    littlewoodBoundary (fun s => (s-ρ)^m) a b c d k = 2*Real.pi*(m:ℝ)*(ρ.re-a) := by sorry

end
end HigherCorrelations
