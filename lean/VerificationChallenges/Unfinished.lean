import HigherCorrelations.Definitions

/-! Deliberately incomplete negative control; never imported by project proofs. -/
namespace HigherCorrelations
theorem zeta_ne_zero_right {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (_hpole : s ≠ 1) : riemannZeta s ≠ 0 := by sorry
end HigherCorrelations
