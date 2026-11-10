import HigherCorrelations.LittlewoodMollified
import HigherCorrelations.LittlewoodExamples

/-! UNCONDITIONAL product checks: repeated/shared zeros, added zeros, strict
thresholds, constant factors, and exclusion of the zero mollifier. -/
namespace HigherCorrelations
noncomputable section
open Complex Set
open scoped Classical

theorem littlewood_product_zero_impossible (f : ℂ → ℂ) (a b c d : ℝ) :
    ¬ LittlewoodRectangle (f*0) a b c d := by
  intro h
  have hn := (h.horizontal c (Or.inl rfl) b ⟨h.horizontal_lt.le,le_rfl⟩).2
  simpa using hn

theorem littlewood_product_one_boundary (f : ℂ → ℂ) (a b c d : ℝ) (k : ℂ) :
    littlewoodBoundary (f*1) a b c d k = littlewoodBoundary f a b c d k := by simp

theorem littlewood_mollified_one {a σ c d : ℝ}
    (hz : LittlewoodRectangle riemannZeta a 2 c d) (ha : 0 < a) (hσ : a < σ)
    (k : ℂ) (hk : exp k = riemannZeta (2+c*I)) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤
      littlewoodBoundary (riemannZeta*1) a 2 c d k / (2*Real.pi*(σ-a)) := by
  have h1 : LittlewoodRectangle (1 : ℂ → ℂ) a 2 c d :=
    ⟨hz.horizontal_lt,hz.vertical_lt,fun _ _ => analyticAt_const,by simp⟩
  exact littlewood_mollified_bound hz h1 ha hσ k (by simpa using hk)

theorem littlewood_product_constant_count {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : LittlewoodRectangle f a b c d) (w : ℂ) (hw : w ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ s ∈ Z, s ∈ Rectangle (a+c*I) (b+d*I)) (σ : ℝ) :
    littlewoodRightCount (f*(fun _ => w)) Z σ = littlewoodRightCount f Z σ := by
  have hg : LittlewoodRectangle (fun _ => w) a b c d :=
    ⟨hf.horizontal_lt,hf.vertical_lt,by fun_prop,fun _ _ => hw⟩
  unfold littlewoodRightCount
  apply Finset.sum_congr rfl
  intro s hs
  rw [littlewood_product_order hf hg s (hZ s (Finset.mem_filter.mp hs).1)]
  have ho : analyticOrderAt (fun _ : ℂ => w) s = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hw)
  simp [analyticOrderNatAt,ho]

private theorem power_order (p s : ℂ) (m : ℕ) :
    analyticOrderNatAt (fun z : ℂ => (z-p)^m) s = if s=p then m else 0 := by
  change analyticOrderNatAt ((·-p)^m) s = _
  rw [analyticOrderNatAt_pow (by fun_prop)]
  by_cases he : s=p
  · subst s
    simp [analyticOrderNatAt]
  · simp [he,analyticOrderNatAt,analyticOrderAt_id_sub_const_of_ne he]

private theorem power_order_finite (p s : ℂ) (m : ℕ) :
    analyticOrderAt (fun z : ℂ => (z-p)^m) s ≠ ⊤ := by
  change analyticOrderAt ((·-p)^m) s ≠ ⊤
  rw [analyticOrderAt_pow (by fun_prop)]
  by_cases he : s=p
  · subst s; simp
  · simp [analyticOrderAt_id_sub_const_of_ne he]

private theorem two_power_order (p q s : ℂ) (m n : ℕ) :
    analyticOrderNatAt (fun z : ℂ => (z-p)^m*(z-q)^n) s =
      (if s=p then m else 0)+(if s=q then n else 0) := by
  change analyticOrderNatAt ((fun z : ℂ => (z-p)^m)*(fun z : ℂ => (z-q)^n)) s = _
  rw [analyticOrderNatAt_mul (by fun_prop) (by fun_prop)
    (power_order_finite p s m) (power_order_finite q s n),power_order,power_order]

theorem littlewood_product_shared_root (p : ℂ) (m n : ℕ) (σ : ℝ) :
    littlewoodRightCount (fun z : ℂ => (z-p)^m*(z-p)^n) {p} σ =
      if σ<p.re then m+n else 0 := by
  unfold littlewoodRightCount
  by_cases hσ : σ<p.re <;> simp [Finset.sum_filter,hσ,two_power_order]

theorem littlewood_product_added_root (p q : ℂ) (hpq : p ≠ q) (m n : ℕ) (σ : ℝ) :
    littlewoodRightCount (fun z : ℂ => (z-p)^m*(z-q)^n) {p,q} σ =
      (if σ<p.re then m else 0)+(if σ<q.re then n else 0) := by
  unfold littlewoodRightCount
  by_cases hp : σ<p.re <;> by_cases hq : σ<q.re <;>
    simp [Finset.sum_filter,hp,hq,hpq,hpq.symm,two_power_order]

theorem littlewood_product_shared_threshold (p : ℂ) (m n : ℕ) :
    littlewoodRightCount (fun z : ℂ => (z-p)^m*(z-p)^n) {p} p.re = 0 := by
  simp [littlewood_product_shared_root]

end
end HigherCorrelations
