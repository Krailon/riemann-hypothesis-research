import HigherCorrelations.LittlewoodCounting

/-! UNCONDITIONAL. Products retain analytic multiplicities. Boundary
nonvanishing supplies finite orders; interior zeros of either factor are allowed. -/
namespace HigherCorrelations
noncomputable section
open Complex Set
open scoped Classical

theorem LittlewoodRectangle.mul {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : LittlewoodRectangle f a b c d) (hg : LittlewoodRectangle g a b c d) :
    LittlewoodRectangle (f*g) a b c d :=
  ⟨hf.horizontal_lt,hf.vertical_lt,hf.analytic.mul hg.analytic,
    fun s hs => mul_ne_zero (hf.nonzero s hs) (hg.nonzero s hs)⟩

theorem littlewood_product_factors {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : AnalyticOnNhd ℂ f (Rectangle (a+c*I) (b+d*I)))
    (hg : AnalyticOnNhd ℂ g (Rectangle (a+c*I) (b+d*I)))
    (h : LittlewoodRectangle (f*g) a b c d) :
    LittlewoodRectangle f a b c d ∧ LittlewoodRectangle g a b c d := by
  constructor
  · exact ⟨h.horizontal_lt,h.vertical_lt,hf,fun s hs =>
      (mul_ne_zero_iff.mp (h.nonzero s hs)).1⟩
  · exact ⟨h.horizontal_lt,h.vertical_lt,hg,fun s hs =>
      (mul_ne_zero_iff.mp (h.nonzero s hs)).2⟩

theorem LittlewoodRectangle.order_finite {f : ℂ → ℂ} {a b c d : ℝ}
    (h : LittlewoodRectangle f a b c d) (s : ℂ)
    (hs : s ∈ Rectangle (a+c*I) (b+d*I)) : analyticOrderAt f s ≠ ⊤ := by
  have hc : (b:ℂ)+c*I ∈ Rectangle (a+c*I) (b+d*I) := by
    simp [Rectangle,mem_reProdIm,uIcc_of_le,h.horizontal_lt.le,h.vertical_lt.le]
  have hn := (h.horizontal c (Or.inl rfl) b ⟨h.horizontal_lt.le,le_rfl⟩).2
  have hconv : Convex ℝ (Rectangle (a+c*I) (b+d*I)) := by
    rw [rectangle_eq_convexHull]
    exact convex_convexHull ℝ _
  apply h.analytic.analyticOrderAt_ne_top_of_isPreconnected hconv.isPreconnected hc hs
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hn)]
  exact ENat.zero_ne_top

theorem littlewood_product_order {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : LittlewoodRectangle f a b c d) (hg : LittlewoodRectangle g a b c d)
    (s : ℂ) (hs : s ∈ Rectangle (a+c*I) (b+d*I)) :
    analyticOrderNatAt (f*g) s = analyticOrderNatAt f s + analyticOrderNatAt g s :=
  analyticOrderNatAt_mul (hf.analytic s hs) (hg.analytic s hs)
    (hf.order_finite s hs) (hg.order_finite s hs)

theorem littlewood_product_order_le {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : LittlewoodRectangle f a b c d) (hg : LittlewoodRectangle g a b c d)
    (s : ℂ) (hs : s ∈ Rectangle (a+c*I) (b+d*I)) :
    analyticOrderNatAt f s ≤ analyticOrderNatAt (f*g) s := by
  rw [littlewood_product_order hf hg s hs]
  omega

private theorem count_enlarge (f : ℂ → ℂ) (Z W : Finset ℂ) (σ : ℝ)
    (hZW : Z ⊆ W) (hn : ∀ s ∈ W, s ∉ Z → f s ≠ 0) :
    littlewoodRightCount f Z σ = littlewoodRightCount f W σ := by
  unfold littlewoodRightCount
  apply Finset.sum_subset (Finset.filter_subset_filter _ hZW)
  intro s hs hs'
  have hw := Finset.mem_filter.mp hs
  have hz : s ∉ Z := by
    intro hz; exact hs' (Finset.mem_filter.mpr ⟨hz,hw.2⟩)
  simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr (hn s hw.1 hz))]

theorem littlewood_product_zero_set {f g : ℂ → ℂ} {a b c d : ℝ}
    (Zf Zg : Finset ℂ)
    (hZf : ∀ s, s ∈ Zf ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0)
    (hZg : ∀ s, s ∈ Zg ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ g s = 0) :
    ∀ s, s ∈ Zf ∪ Zg ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ (f*g) s = 0 := by
  intro s
  simp only [Finset.mem_union, hZf, hZg, Pi.mul_apply, mul_eq_zero]
  tauto

theorem littlewood_product_count_add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : LittlewoodRectangle f a b c d) (hg : LittlewoodRectangle g a b c d)
    (Zf Zg Z : Finset ℂ)
    (hZf : ∀ s, s ∈ Zf ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0)
    (hZg : ∀ s, s ∈ Zg ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ g s = 0)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ (f*g) s = 0)
    (σ : ℝ) :
    littlewoodRightCount (f*g) Z σ = littlewoodRightCount f Zf σ + littlewoodRightCount g Zg σ := by
  have hsf : Zf ⊆ Z := by
    intro s hs
    rcases (hZf s).mp hs with ⟨hr,hzero⟩
    exact (hZ s).mpr ⟨hr,by simp [hzero]⟩
  have hsg : Zg ⊆ Z := by
    intro s hs
    rcases (hZg s).mp hs with ⟨hr,hzero⟩
    exact (hZ s).mpr ⟨hr,by simp [hzero]⟩
  rw [count_enlarge f Zf Z σ hsf (by
    intro s hs hn hz; exact hn ((hZf s).mpr ⟨((hZ s).mp hs).1,hz⟩)),
    count_enlarge g Zg Z σ hsg (by
    intro s hs hn hz; exact hn ((hZg s).mpr ⟨((hZ s).mp hs).1,hz⟩))]
  unfold littlewoodRightCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  exact littlewood_product_order hf hg s ((hZ s).mp (Finset.mem_filter.mp hs).1).1

theorem littlewood_product_count_le {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : LittlewoodRectangle f a b c d) (hg : LittlewoodRectangle g a b c d)
    (Zf Zg Z : Finset ℂ)
    (hZf : ∀ s, s ∈ Zf ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ f s = 0)
    (hZg : ∀ s, s ∈ Zg ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ g s = 0)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ (f*g) s = 0)
    (σ : ℝ) : littlewoodRightCount f Zf σ ≤ littlewoodRightCount (f*g) Z σ := by
  rw [littlewood_product_count_add hf hg Zf Zg Z hZf hZg hZ σ]
  omega

end
end HigherCorrelations
