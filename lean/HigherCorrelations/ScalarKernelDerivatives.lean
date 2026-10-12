import HigherCorrelations.ScalarKernel
import Mathlib.Analysis.Complex.RealDeriv

/-! UNCONDITIONAL scalar horizontal jets and explicit decay bounds. -/
namespace HigherCorrelations
noncomputable section

theorem scalar_poles_ne_zero (x e : ℝ) (he : |e| ≤ 3/4) :
    (x : ℂ) + Complex.I*e - Complex.I ≠ 0 ∧
    (x : ℂ) + Complex.I*e + Complex.I ≠ 0 := by
  rcases abs_le.mp he with ⟨hl,hu⟩
  constructor <;> intro h <;> have hi := congrArg Complex.im h <;> simp at hi <;> linarith

theorem scalarKernelJet_zero (x e : ℝ) (he : |e| ≤ 3/4) :
    scalarKernelJet 0 x e = scalarKernel x e := by
  obtain ⟨h₁,h₂⟩ := scalar_poles_ne_zero x e he
  have hd := scalar_denominator_ne_zero x e he
  unfold scalarKernelJet scalarKernel
  norm_num only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, pow_one]
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem scalarKernelJet_hasDerivAt (n : ℕ) (x e : ℝ) (he : |e| ≤ 3/4) :
    HasDerivAt (scalarKernelJet n x) (scalarKernelJet (n+1) x e) e := by
  obtain ⟨h₁,h₂⟩ := scalar_poles_ne_zero x e he
  have hu : HasDerivAt (fun e : ℝ => (x : ℂ) + Complex.I*e - Complex.I) Complex.I e := by
    simpa using ((Complex.ofRealCLM.hasDerivAt.const_mul Complex.I).const_add (x : ℂ)).sub_const Complex.I
  have hl : HasDerivAt (fun e : ℝ => (x : ℂ) + Complex.I*e + Complex.I) Complex.I e := by
    simpa using ((Complex.ofRealCLM.hasDerivAt.const_mul Complex.I).const_add (x : ℂ)).add_const Complex.I
  have h := (((hu.inv h₁).pow (n+1)).sub ((hl.inv h₂).pow (n+1))).const_mul
    ((-Complex.I)^n * (n.factorial : ℂ) / (2*Complex.I))
  simp only [Pi.pow_apply, Pi.inv_apply, Pi.sub_apply] at h
  change HasDerivAt (scalarKernelJet n x) _ e at h
  convert h using 1
  unfold scalarKernelJet
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
  field_simp
  ring

theorem shifted_inverse_bounds (x y : ℝ) (hy : 1/4 ≤ |y|) :
    ‖((x : ℂ)+Complex.I*y)⁻¹‖ ≤ 4 ∧
    ‖((x : ℂ)+Complex.I*y)⁻¹‖^2 ≤ 16/(1+x^2) := by
  have hs : ‖((x : ℂ)+Complex.I*y)‖^2 = x^2+y^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  have hy2 : (1/16 : ℝ) ≤ y^2 := by nlinarith [sq_abs y]
  have hn : 0 < ‖((x : ℂ)+Complex.I*y)‖ := by
    nlinarith [norm_nonneg ((x : ℂ)+Complex.I*y), sq_nonneg x]
  rw [norm_inv]
  constructor
  · rw [inv_eq_one_div]
    apply (div_le_iff₀ hn).mpr
    nlinarith [norm_nonneg ((x : ℂ)+Complex.I*y), sq_nonneg x]
  · rw [inv_pow, hs, inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg x]

theorem shifted_inverse_power_bound (n : ℕ) (x y : ℝ) (hy : 1/4 ≤ |y|) :
    ‖(((x : ℂ)+Complex.I*y)⁻¹)^(n+2)‖ ≤ 4^(n+2)/(1+x^2) := by
  obtain ⟨hb,hs⟩ := shifted_inverse_bounds x y hy
  rw [norm_pow, pow_add]
  calc
    _ ≤ 4^n * (16/(1+x^2)) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hb n) hs
      (sq_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; norm_num; ring

theorem scalarKernelJet_bound (n : ℕ) (x e : ℝ) (he : |e| ≤ 3/4) :
    ‖scalarKernelJet n x e‖ ≤ 4^(n+1) * n.factorial / (1+x^2) := by
  cases n with
  | zero => simpa [scalarKernelJet_zero x e he] using scalarKernel_bound x e he
  | succ n =>
    rcases abs_le.mp he with ⟨he₁,he₂⟩
    have hm : 1/4 ≤ |e-1| := by rw [abs_of_nonpos (by linarith)]; linarith
    have hp : 1/4 ≤ |e+1| := by rw [abs_of_nonneg (by linarith)]; linarith
    have em : (x : ℂ)+Complex.I*e-Complex.I = (x : ℂ)+Complex.I*(e-1 : ℝ) := by push_cast; ring
    have ep : (x : ℂ)+Complex.I*e+Complex.I = (x : ℂ)+Complex.I*(e+1 : ℝ) := by push_cast; ring
    have hb₁ := shifted_inverse_power_bound n x (e-1) hm
    have hb₂ := shifted_inverse_power_bound n x (e+1) hp
    have hc : ‖(-Complex.I)^(n+1) * ((n+1).factorial : ℂ) / (2*Complex.I)‖ =
        ((n+1).factorial : ℝ)/2 := by simp
    change ‖scalarKernelJet (n+1) x e‖ ≤ _
    rw [scalarKernelJet, norm_mul, hc, em, ep]
    calc
      _ ≤ ((n+1).factorial : ℝ)/2 *
          (4^(n+2)/(1+x^2) + 4^(n+2)/(1+x^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (norm_sub_le _ _).trans (add_le_add hb₁ hb₂)
      _ = _ := by ring

end
end HigherCorrelations
