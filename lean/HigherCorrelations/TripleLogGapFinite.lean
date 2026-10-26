import HigherCorrelations.TripleLogGapDefinitions
import HigherCorrelations.TripleLogGapRows
import HigherCorrelations.TripleFiniteSchur

/-! UNCONDITIONAL finite reciprocal-log inequality with the manuscript constant. -/
namespace HigherCorrelations
noncomputable section

theorem tripleComparableKernel_nonneg (m n : ℕ) : 0≤tripleComparableKernel m n := by
  unfold tripleComparableKernel
  split_ifs <;> positivity

theorem tripleComparableKernel_swap (m n : ℕ) :
    tripleComparableKernel m n = tripleComparableKernel n m := by
  simp only [tripleComparableKernel,abs_sub_comm,ne_comm]
  congr 1
  exact propext (by tauto)

theorem tripleComparableKernel_row (s : Finset ℕ) (m : ℕ) (hm : 2≤m) :
    (∑ n ∈ s, tripleComparableKernel m n) ≤ 4*Real.log (2*m) := by
  unfold tripleComparableKernel
  rw [← Finset.sum_filter]
  exact tripleLogGap_row _ m hm (fun n hn => by
    have h := (Finset.mem_filter.mp hn).2
    exact ⟨h.2.1,h.2.2.symm⟩)

theorem tripleLogGap_term (m n : ℕ) (hm : 2≤m) (hn : 2≤n) (a b : ℝ)
    (ha : 0≤a) (hb : 0≤b) :
    (if m=n then 0 else a*b/|Real.log ((m:ℝ)/n)|) ≤
      a*b/Real.log 2 + Real.sqrt 2 *
        (tripleComparableKernel m n*(Real.sqrt m*a)*(Real.sqrt n*b)) := by
  have hm0 : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  by_cases he : m=n
  · simp only [if_pos he]
    positivity [tripleComparableKernel_nonneg m n,Real.log_pos (by norm_num : (1:ℝ)<2)]
  rw [if_neg he]
  by_cases hc : m≤2*n ∧ n≤2*m ∧ m≠n
  · have hg := tripleLogGap_comparable (m:ℝ) n hm0 hn0 (by exact_mod_cast he)
      (by exact_mod_cast (show (m:ℝ)/2≤n by
        have h : (m:ℝ)≤2*n := by exact_mod_cast hc.1
        linarith)) (by exact_mod_cast hc.2.1)
    have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg ha hb)
    have hbound : a*b/|Real.log ((m:ℝ)/n)| ≤ Real.sqrt 2 *
        (tripleComparableKernel m n*(Real.sqrt m*a)*(Real.sqrt n*b)) := by
      simpa only [tripleComparableKernel,if_pos hc] using
        (show a*b/|Real.log ((m:ℝ)/n)| ≤ Real.sqrt 2 *
          (1/|(m:ℝ)-n| *(Real.sqrt m*a)*(Real.sqrt n*b)) by convert hh using 1 <;> ring)
    exact hbound.trans (le_add_of_nonneg_left (div_nonneg (mul_nonneg ha hb) (Real.log_nonneg (by norm_num))))
  · have hfar : (n:ℝ)<(m:ℝ)/2 ∨ 2*(m:ℝ)<n := by
      by_cases hmn : m≤2*n
      · right
        have h : 2*m<n := by omega
        exact_mod_cast h
      · left
        have h : (2:ℝ)*n<m := by exact_mod_cast (show 2*n<m by omega)
        linarith
    have hh := mul_le_mul_of_nonneg_left (tripleLogGap_far (m:ℝ) n hm0 hn0 hfar) (mul_nonneg ha hb)
    simpa [tripleComparableKernel,hc,div_eq_mul_inv,mul_assoc] using hh

theorem tripleLogGap_finite (s t : Finset ℕ) (hs : ∀ m ∈ s, 2≤m) (ht : ∀ n ∈ t, 2≤n)
    (a b : ℕ → ℝ) (ha : ∀ m, 0≤a m) (hb : ∀ n, 0≤b n) :
    (∑ m ∈ s, ∑ n ∈ t, if m=n then 0 else a m*b n/|Real.log ((m:ℝ)/n)|) ≤
      (∑ m ∈ s, a m)*(∑ n ∈ t, b n)/Real.log 2 + 4*Real.sqrt 2 *
        Real.sqrt ((∑ m ∈ s, (m:ℝ)*Real.log (2*m)*a m^2)*
          (∑ n ∈ t, (n:ℝ)*Real.log (2*n)*b n^2)) := by
  have hpoint := Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn =>
    tripleLogGap_term m n (hs m hm) (ht n hn) (a m) (b n) (ha m) (hb n)))
  have hschur := tripleFiniteSchur s t tripleComparableKernel
    (fun m => Real.sqrt m*a m) (fun n => Real.sqrt n*b n)
    (fun m => 4*Real.log (2*m)) (fun n => 4*Real.log (2*n))
    (fun m _ n _ => tripleComparableKernel_nonneg m n)
    (fun m hm => tripleComparableKernel_row t m (hs m hm))
    (fun n hn => by simpa only [tripleComparableKernel_swap] using tripleComparableKernel_row s n (ht n hn))
  have hea : (∑ m ∈ s, 4*Real.log (2*m)*(Real.sqrt m*a m)^2) =
      4*(∑ m ∈ s, (m:ℝ)*Real.log (2*m)*a m^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have heb : (∑ n ∈ t, 4*Real.log (2*n)*(Real.sqrt n*b n)^2) =
      4*(∑ n ∈ t, (n:ℝ)*Real.log (2*n)*b n^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  rw [hea,heb,show ∀ A B : ℝ, (4*A)*(4*B)=16*(A*B) by intros; ring,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤16)] at hschur
  norm_num at hschur
  have he : (∑ m ∈ s, ∑ n ∈ t, (a m*b n/Real.log 2 + Real.sqrt 2 *
      (tripleComparableKernel m n*(Real.sqrt m*a m)*(Real.sqrt n*b n)))) =
      (∑ m ∈ s, a m)*(∑ n ∈ t, b n)/Real.log 2 + Real.sqrt 2 *
        (∑ m ∈ s, ∑ n ∈ t, tripleComparableKernel m n*(Real.sqrt m*a m)*(Real.sqrt n*b n)) := by
    simp only [Finset.sum_add_distrib,← Finset.sum_div,← Finset.mul_sum,← Finset.sum_mul]
  rw [he] at hpoint
  exact hpoint.trans (by nlinarith [Real.sqrt_nonneg 2])

end
end HigherCorrelations
