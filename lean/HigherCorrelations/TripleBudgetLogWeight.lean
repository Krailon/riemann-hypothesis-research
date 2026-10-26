import HigherCorrelations.TripleBudgetMoments

/-! UNCONDITIONAL compact log weights: endpoint vanishing and derivative budget. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem tripleBudgetLogWeight_support (ω : ℝ → ℝ) (T : ℝ) (r : ℕ) :
    tsupport (tripleBudgetLogWeight ω T r) ⊆ tsupport ω := by
  apply closure_mono
  intro u hu
  intro hz
  exact hu (by simp [tripleBudgetLogWeight,hz])

theorem tripleBudgetLogWeight_smooth (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤T) (r : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (tripleBudgetLogWeight ω T r) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u∈tsupport ω
  · have hs := hω.support hu
    exact hω.smooth.contDiffAt.mul
      ((((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).log
        (by nlinarith [hs.1] : T*u+2≠0)).pow r)
  · have he : tripleBudgetLogWeight ω T r =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hu] with v hv
      simp [tripleBudgetLogWeight,hv]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem tripleBudgetLogWeight_compact (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (r : ℕ) : HasCompactSupport (tripleBudgetLogWeight ω T r) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro u hu
  exact Ioo_subset_Icc_self (hω.support (tripleBudgetLogWeight_support ω T r (subset_tsupport _ hu)))

theorem tripleBudgetLogWeight_deriv (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤T) (r : ℕ) (u : ℝ) (hu : u∈tsupport ω) :
    deriv (tripleBudgetLogWeight ω T r) u =
      deriv ω u*Real.log (T*u+2)^r + ω u*((r:ℝ)*Real.log (T*u+2)^(r-1)*(T/(T*u+2))) := by
  have hs := hω.support hu
  have hw := (hω.smooth.differentiable (by simp) u).hasDerivAt
  have hl := (((hasDerivAt_id u).const_mul T).add_const 2).log (by nlinarith [hs.1] : T*u+2≠0)
  have he := (hw.mul (hl.pow r)).deriv
  change deriv (tripleBudgetLogWeight ω T r) u = _ at he
  simpa only [mul_one,id_eq,Pi.pow_apply] using he

theorem tripleBudgetLogWeight_deriv_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤T) (r : ℕ) (u : ℝ) :
    |deriv (tripleBudgetLogWeight ω T r) u| ≤
      |deriv ω u| *Real.log (2*T+2)^r + ω u*((r:ℝ)*Real.log (2*T+2)^(r-1)) := by
  by_cases hu : u∈tsupport ω
  · have hs := hω.support hu
    have hpos : 0<T*u+2 := by nlinarith [hs.1]
    have hl : 0≤Real.log (T*u+2) := Real.log_nonneg (by nlinarith [hs.1])
    have hL : Real.log (T*u+2)≤Real.log (2*T+2) := Real.log_le_log hpos (by nlinarith [hs.2])
    have hratio : 0≤T/(T*u+2) ∧ T/(T*u+2)≤1 :=
      ⟨by positivity,(div_le_one hpos).mpr (by nlinarith [hs.1])⟩
    rw [tripleBudgetLogWeight_deriv ω hω T hT r u hu]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg (pow_nonneg hl r),abs_of_nonneg (by positivity [hω.nonneg u] :
      0≤ω u*((r:ℝ)*Real.log (T*u+2)^(r-1)*(T/(T*u+2))))]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hL r) (abs_nonneg _)
    · apply mul_le_mul_of_nonneg_left _ (hω.nonneg u)
      calc
        _ ≤ (r:ℝ)*Real.log (2*T+2)^(r-1)*1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hL (r-1)) (Nat.cast_nonneg _))
            hratio.2 hratio.1 (by positivity [hl.trans hL])
        _ = _ := mul_one _
  · have hz := image_eq_zero_of_notMem_tsupport hu
    have hd := deriv_of_notMem_tsupport hu
    have hw : u∉tsupport (tripleBudgetLogWeight ω T r) := fun h => hu (tripleBudgetLogWeight_support ω T r h)
    simp only [deriv_of_notMem_tsupport hw,hd,hz,abs_zero,zero_mul,zero_add,le_refl]

theorem tripleBudgetOmega_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤T) (r : ℕ) :
    tripleBudgetOmega ω T r ≤ fourierDerivativeL1 ω 1*Real.log (2*T+2)^r + (r:ℝ)*Real.log (2*T+2)^(r-1) := by
  have hcω : HasCompactSupport ω := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (tripleBudgetWeight_support ω hω)
  have hdc : Continuous (deriv ω) := by simpa only [iteratedDeriv_one] using hω.smooth.continuous_iteratedDeriv 1 (by simp)
  have hdi : Integrable (fun u => |deriv ω u|) := (hdc.integrable_of_hasCompactSupport hcω.deriv).abs
  have hwl := tripleBudgetLogWeight_smooth ω hω T hT r
  have hdwl : Continuous (deriv (tripleBudgetLogWeight ω T r)) := by
    simpa only [iteratedDeriv_one] using hwl.continuous_iteratedDeriv 1 (by simp)
  have hil : Integrable (fun u => |deriv (tripleBudgetLogWeight ω T r) u|) := (hdwl.integrable_of_hasCompactSupport (tripleBudgetLogWeight_compact ω hω T r).deriv).abs
  have hi1 := hdi.mul_const (Real.log (2*T+2)^r)
  have hi2 := (tripleBudgetWeight_integrable ω hω).mul_const ((r:ℝ)*Real.log (2*T+2)^(r-1))
  have h := integral_mono hil (hi1.add hi2) (tripleBudgetLogWeight_deriv_bound ω hω T hT r)
  simpa only [Pi.add_apply,integral_add hi1 hi2,integral_mul_const,hω.mass,one_mul,tripleBudgetOmega,
    fourierDerivativeL1,iteratedDeriv_one] using h

end
end HigherCorrelations
