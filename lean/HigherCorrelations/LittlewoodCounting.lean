import HigherCorrelations.LittlewoodBoundary
import Zeta23.Analytic.RectangleLogDeriv

/-! UNCONDITIONAL. Littlewood identity and strict multiplicity-weighted horizontal counts. -/
namespace HigherCorrelations
noncomputable section
open Complex Set MeasureTheory
open scoped Classical

theorem littlewood_zero_set_exists {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) :
    ∃ Z : Finset ℂ, ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0 := by
  have hm : (b:ℂ)+c*I ∈ Rectangle (a+c*I) (b+d*I) := by
    simp [Rectangle, mem_reProdIm, uIcc_of_le, h.horizontal_lt.le, h.vertical_lt.le]
  have hf := Zeta23.Analytic.finite_zeros_rectangle h.analytic hm
    (h.horizontal c (Or.inl rfl) b ⟨h.horizontal_lt.le,le_rfl⟩).2
  exact ⟨hf.toFinset,by intro s; simp⟩

theorem littlewood_weighted_argument {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0) :
    (RectangleIntegral (fun s => (s-(a+c*I))*logDeriv f s) (a+c*I) (b+d*I)).im =
      2*Real.pi*littlewoodMass f Z a := by
  have hh := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv
    (by simpa using h.horizontal_lt.le) (by simpa using h.vertical_lt.le)
    h.analytic (show AnalyticOnNhd ℂ (fun s => s-(a+c*I)) _ from by fun_prop)
    h.nonzero Z (fun s hs => ⟨fun hz => (hZ s).mpr ⟨hs,hz⟩,fun hz => ((hZ s).mp hz).2⟩)
    (fun s hs => ((hZ s).mp hs).1)
  have he := congrArg (fun w : ℂ => (2*Real.pi*I)*w) hh
  have hn : (2*Real.pi*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [RectangleIntegral', smul_eq_mul, one_div] at he
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul] at he
  have hi := congrArg Complex.im he
  simpa [littlewoodMass, mul_im, mul_re, sub_re, Complex.re_sum] using hi

theorem littlewood_identity {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0)
    (k : ℂ) (hk : exp k = f (b+c*I)) :
    2*Real.pi*littlewoodMass f Z a = littlewoodBoundary f a b c d k := by
  rw [← littlewood_weighted_argument h Z hZ, littlewood_boundary_integral h k hk]

theorem littlewood_mass_count (f : ℂ → ℂ) (Z : Finset ℂ) (a σ : ℝ)
    (hσ : a < σ) (hZ : ∀ s ∈ Z, a ≤ s.re) :
    (σ-a)*(littlewoodRightCount f Z σ : ℝ) ≤ littlewoodMass f Z a := by
  have hnonneg : ∀ s ∈ Z, 0 ≤ (analyticOrderNatAt f s : ℝ)*(s.re-a) := by
    intro s hs; exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hZ s hs))
  unfold littlewoodRightCount littlewoodMass
  push_cast
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ s ∈ Z.filter (fun s => σ < s.re), (analyticOrderNatAt f s : ℝ)*(s.re-a) := by
      apply Finset.sum_le_sum
      intro s hs
      have hd := (Finset.mem_filter.mp hs).2
      nlinarith [show (0:ℝ) ≤ (analyticOrderNatAt f s : ℝ) from Nat.cast_nonneg _]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s hs _ => hnonneg s hs)

theorem littlewood_count_bound {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0)
    (k : ℂ) (hk : exp k = f (b+c*I)) (σ : ℝ) (hσ : a < σ) :
    (littlewoodRightCount f Z σ : ℝ) ≤ littlewoodBoundary f a b c d k / (2*Real.pi*(σ-a)) := by
  have hm := littlewood_mass_count f Z a σ hσ (by
    intro s hs
    have hh := ((hZ s).mp hs).1
    simpa [Rectangle, mem_reProdIm, uIcc_of_le, h.horizontal_lt.le, h.vertical_lt.le] using hh |>.1.1)
  have hi := littlewood_identity h Z hZ k hk
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi*(σ-a))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*Real.pi by positivity)]

theorem littlewood_count_of_budget {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0)
    (k : ℂ) (hk : exp k = f (b+c*I)) (σ E : ℝ) (hσ : a < σ)
    (hE : littlewoodBoundary f a b c d k ≤ E) :
    (littlewoodRightCount f Z σ : ℝ) ≤ E / (2*Real.pi*(σ-a)) :=
  (littlewood_count_bound h Z hZ k hk σ hσ).trans
    (div_le_div_of_nonneg_right hE (by positivity))

theorem littlewood_boundary_branch_invariant {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (k l : ℂ)
    (hk : exp k = f (b+c*I)) (hl : exp l = f (b+c*I)) :
    littlewoodBoundary f a b c d k = littlewoodBoundary f a b c d l := by
  obtain ⟨Z,hZ⟩ := littlewood_zero_set_exists h
  rw [← littlewood_identity h Z hZ k hk, ← littlewood_identity h Z hZ l hl]

theorem littlewood_count_threshold (f : ℂ → ℂ) (Z : Finset ℂ) (σ : ℝ)
    (hZ : ∀ s ∈ Z, s.re = σ) : littlewoodRightCount f Z σ = 0 := by
  unfold littlewoodRightCount
  apply Finset.sum_eq_zero
  intro s hs
  have hh := Finset.mem_filter.mp hs
  have := hZ s hh.1
  exact False.elim (by linarith [hh.2])

end
end HigherCorrelations
