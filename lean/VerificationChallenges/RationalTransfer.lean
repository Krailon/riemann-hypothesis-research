import HigherCorrelations.RationalTransferDefinitions
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Definition-only Comparator specifications. Intentional unfinished proofs;
solution modules never import this file. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology ContDiff

theorem rational_denominator_lower (z : ℂ) (hz : |z.im| ≤ 1) :
    3 + z.re ^ 2 ≤ ‖4 + z ^ 2‖ := by sorry

theorem rational_denominator_ne_zero (z : ℂ) (hz : |z.im| ≤ 1) :
    4 + z ^ 2 ≠ 0 := by sorry

theorem rationalKernel_reciprocal (z₁ z₂ z₃ : ℂ)
    (h₁₂ : 4 + (z₁-z₂)^2 ≠ 0) (h₁₃ : 4 + (z₁-z₃)^2 ≠ 0)
    (h₂₃ : 4 + (z₂-z₃)^2 ≠ 0) :
    rationalKernel z₁ z₂ z₃ = (Real.pi : ℂ) *
      (1 / ((4+(z₁-z₂)^2)*(4+(z₁-z₃)^2)) +
       1 / ((4+(z₁-z₂)^2)*(4+(z₂-z₃)^2)) +
       1 / ((4+(z₁-z₃)^2)*(4+(z₂-z₃)^2)) +
       12 / ((4+(z₁-z₂)^2)*(4+(z₁-z₃)^2)*(4+(z₂-z₃)^2))) := by sorry

theorem rationalKernel_bound (z₁ z₂ z₃ : ℂ)
    (h₁ : |z₁.im| ≤ 1/2) (h₂ : |z₂.im| ≤ 1/2) (h₃ : |z₃.im| ≤ 1/2) :
    ‖rationalKernel z₁ z₂ z₃‖ ≤ 7 * Real.pi / 9 := by sorry

theorem rationalProfile_bound (a b e f g : ℝ)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2) (hg : |g| ≤ 1/2) :
    ‖rationalProfile a b e f g‖ ≤ 7 * Real.pi / 9 := by sorry

theorem rationalProfile_swap (a b e f g : ℝ) :
    rationalProfile a b e f g = rationalProfile b a f e g := by sorry

theorem rationalProfile_conj (a b e f g : ℝ) :
    rationalProfile a b (-e) (-f) (-g) = star (rationalProfile a b e f g) := by sorry

theorem rationalProfile_origin : rationalProfile 0 0 0 0 0 = kernelBenchmark := by sorry

theorem rationalProfile_coincident (e : ℝ) : rationalProfile 0 0 e e (-e) = kernelBenchmark := by sorry

theorem rationalProfile_real (a b : ℝ) :
    rationalProfile a b 0 0 0 =
      ((Real.pi * (24 + (a-b)^2 + a^2 + b^2) /
        ((4+(a-b)^2)*(4+a^2)*(4+b^2)) : ℝ) : ℂ) := by sorry

theorem rational_denominator_endpoint (x : ℝ) :
    3 + x^2 ≤ ‖4 + ((x : ℂ) + Complex.I)^2‖ := by sorry

theorem actualRationalKernel_bound (t : Fin 3 → ZeroOccurrence) :
    ‖actualRationalKernel t‖ ≤ 7 * Real.pi / 9 := by sorry

theorem actualRealKernel_bound (t : Fin 3 → ZeroOccurrence) :
    ‖actualRealKernel t‖ ≤ 7 * Real.pi / 9 := by sorry

theorem bounded_kernel_summable_norm {I : Type*} (f K : I → ℂ) (C : ℝ)
    (_hC : 0 ≤ C) (hK : ∀ i, ‖K i‖ ≤ C) (hf : Summable (fun i => ‖f i‖)) :
    Summable (fun i => ‖K i * f i‖) := by sorry

theorem rationalTransferTerm_summable (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (k : TransferTermKind) :
    Summable (fun t => ‖rationalTransferTerm a w φ k t‖) := by sorry

theorem rationalTransferTerm_cutoff_limit (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (k : TransferTermKind) :
    Tendsto (fun N : Fin 3 → ℕ => ∑ t ∈ tripleDomain (fun j => occurrenceCutoff (N j)),
      rationalTransferTerm a w φ k t) atTop (𝓝 (∑' t, rationalTransferTerm a w φ k t)) := by sorry

theorem rationalTransferSum_cutoff_limit (T : ℝ) (hT : 2*Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (k : TransferTermKind) :
    Tendsto (fun N : Fin 3 → ℕ =>
      (if k = .ordinate then ordinateCoefficient T else transferCoefficient T) *
      ∑ t ∈ tripleDomain (fun j => occurrenceCutoff (N j)),
        rationalTransferTerm (meanSpacing T) w φ k t) atTop (𝓝 (rationalTransferSum T w φ k)) := by sorry

theorem rationalTransferTerm_telescope (a : ℝ) (w : ℝ → ℂ) (φ : ℝ × ℝ → ℂ)
    (t : Fin 3 → ZeroOccurrence) :
    rationalTransferTerm a w φ .weighted t =
      kernelBenchmark * rationalTransferTerm a w φ .ordinate t +
      rationalTransferTerm a w φ .arguments t + rationalTransferTerm a w φ .horizontal t +
      rationalTransferTerm a w φ .gaps t := by sorry

theorem rationalTransfer_finite_telescope (a : ℝ) (w : ℝ → ℂ) (φ : ℝ × ℝ → ℂ)
    (D : Finset (Fin 3 → ZeroOccurrence)) :
    (∑ t ∈ D, rationalTransferTerm a w φ .weighted t) =
      kernelBenchmark * (∑ t ∈ D, rationalTransferTerm a w φ .ordinate t) +
      (∑ t ∈ D, rationalTransferTerm a w φ .arguments t) +
      (∑ t ∈ D, rationalTransferTerm a w φ .horizontal t) +
      (∑ t ∈ D, rationalTransferTerm a w φ .gaps t) := by sorry

theorem rationalTransfer_tsum_telescope (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∑' t, rationalTransferTerm a w φ .weighted t) =
      kernelBenchmark * (∑' t, rationalTransferTerm a w φ .ordinate t) +
      (∑' t, rationalTransferTerm a w φ .arguments t) +
      (∑' t, rationalTransferTerm a w φ .horizontal t) +
      (∑' t, rationalTransferTerm a w φ .gaps t) := by sorry

theorem scaledAnchorWeight_support (T : ℝ) (hT : 0 < T) (w : ℝ → ℂ)
    (hw : ∀ x, x ∉ Set.Ioo (1 : ℝ) 2 → w x = 0) :
    ∀ γ, γ ∉ Set.Icc T (2*T) → scaledAnchorWeight T w γ = 0 := by sorry

theorem scaledAnchorWeight_endpoints (T : ℝ) (hT : 0 < T) (w : ℝ → ℂ)
    (hw : ∀ x, x ∉ Set.Ioo (1 : ℝ) 2 → w x = 0) :
    scaledAnchorWeight T w T = 0 ∧ scaledAnchorWeight T w (2*T) = 0 := by sorry

theorem transfer_log_pos (T : ℝ) (hT : 2 * Real.pi < T) :
    0 < Real.log T ∧ 0 < Real.log (T / (2 * Real.pi)) := by sorry

theorem transferRatio_ne_zero (T : ℝ) (hT : 2 * Real.pi < T) : transferRatio T ≠ 0 := by sorry

theorem transfer_normalization (T : ℝ) (hT : 2 * Real.pi < T) :
    transferCoefficient T * kernelBenchmark = transferRatio T * ordinateCoefficient T := by sorry

theorem actual_rational_transfer (T : ℝ) (hT : 2 * Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    rationalTransferSum T w φ .weighted =
      transferRatio T * rationalTransferSum T w φ .ordinate +
      rationalTransferSum T w φ .arguments + rationalTransferSum T w φ .horizontal +
      rationalTransferSum T w φ .gaps := by sorry

theorem actual_rational_transfer_benchmark (T : ℝ) (hT : 2 * Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (S : ℂ) :
    rationalTransferSum T w φ .ordinate - S =
      ((Real.log T : ℂ) / Real.log (T / (2 * Real.pi))) *
        (rationalTransferSum T w φ .weighted - S - rationalTransferSum T w φ .arguments -
          rationalTransferSum T w φ .horizontal - rationalTransferSum T w φ .gaps) +
      (((Real.log T : ℂ) / Real.log (T / (2 * Real.pi))) - 1) * S := by sorry

theorem actual_rational_transfer_scaled_anchor (T : ℝ) (hT : 2 * Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ x, x ∉ Set.Ioo (1 : ℝ) 2 → w x = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    rationalTransferSum T (scaledAnchorWeight T w) φ .weighted =
      transferRatio T * rationalTransferSum T (scaledAnchorWeight T w) φ .ordinate +
      rationalTransferSum T (scaledAnchorWeight T w) φ .arguments +
      rationalTransferSum T (scaledAnchorWeight T w) φ .horizontal +
      rationalTransferSum T (scaledAnchorWeight T w) φ .gaps := by sorry

theorem rationalTransferTerm_zero_test (a : ℝ) (w : ℝ → ℂ) (k : TransferTermKind)
    (t : Fin 3 → ZeroOccurrence) : rationalTransferTerm a w (fun _ => 0) k t = 0 := by sorry

theorem rationalTransferSum_zero_test (T : ℝ) (w : ℝ → ℂ) (k : TransferTermKind) :
    rationalTransferSum T w (fun _ => 0) k = 0 := by sorry

end
end HigherCorrelations
