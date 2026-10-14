import HigherCorrelations.PairContourResidues

/-! UNCONDITIONAL classification of zeta zeros outside the open critical strip.
No restriction on the real part of nontrivial zeros is added. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem pairZero_nonpos_classification (z : ℂ) (hzero : riemannZeta z = 0)
    (hz : z.re ≤ 0) : ∃ n : ℕ, z = -2*(n+1:ℂ) := by
  have hcos : Complex.cos ((Real.pi:ℂ)*(1-z)/2) = 0 := by
    by_contra hc
    have hn := Kadiri.riemannZeta_one_sub_ne_zero_of_one_le_re
      (w := 1-z) (by simp; linarith) hc
    apply hn
    simpa using hzero
  obtain ⟨k,hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have he : z = -2*(k:ℂ) := by
    have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hh : (Real.pi:ℂ)*z = (Real.pi:ℂ)*(-2*(k:ℂ)) := by
      linear_combination -2*hk
    exact mul_left_cancel₀ hp hh
  have hkpos : 0 < k := by
    have hr := congrArg Complex.re he
    simp at hr
    have hk0 : (0:ℝ) ≤ (k:ℝ) := by linarith
    have hn : 0 ≤ k := by exact_mod_cast hk0
    have hkne : k ≠ 0 := by
      intro h
      simp [h] at he
      simp [he, riemannZeta_zero] at hzero
    omega
  obtain ⟨n,hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k-1)
  refine ⟨n,?_⟩
  have hkn : k = (n:ℤ)+1 := by omega
  rw [he,hkn]
  push_cast
  ring

theorem pairZero_classification (z : ℂ) (hzero : riemannZeta z = 0) :
    (0 < z.re ∧ z.re < 1) ∨ ∃ n : ℕ, z = -2*(n+1:ℂ) := by
  by_cases hz : 0 < z.re
  · left
    refine ⟨hz,?_⟩
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hzero
  · exact Or.inr (pairZero_nonpos_classification z hzero (le_of_not_gt hz))

theorem pairZeta_oddLeft_ne_zero (M : ℕ) (v : ℝ) :
    riemannZeta (-(2*(M:ℂ)+1)+(v:ℂ)*I) ≠ 0 := by
  intro hz
  have hM := Nat.cast_nonneg (α:=ℝ) M
  obtain ⟨n,hn⟩ := pairZero_nonpos_classification _ hz (by simp; linarith)
  have hr := congrArg Complex.re hn
  simp at hr
  have he : 2*(M:ℤ)+1 = 2*((n:ℤ)+1) := by exact_mod_cast (by linarith : 2*(M:ℝ)+1=2*((n:ℝ)+1))
  omega

end
end HigherCorrelations
