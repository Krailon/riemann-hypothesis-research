import HigherCorrelations.RationalKernelBounds

/-! UNCONDITIONAL. Actual rationally weighted sums at fixed height, with independent
inclusive cutoffs. No uniform height estimate or integral/sum interchange. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology ContDiff

theorem bounded_kernel_summable_norm {I : Type*} (f K : I → ℂ) (C : ℝ)
    (_hC : 0 ≤ C) (hK : ∀ i, ‖K i‖ ≤ C) (hf : Summable (fun i => ‖f i‖)) :
    Summable (fun i => ‖K i * f i‖) := by
  apply (hf.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _)

theorem rationalTransferTerm_summable (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (k : TransferTermKind) :
    Summable (fun t => ‖rationalTransferTerm a w φ k t‖) := by
  have hr := actual_summable_norm T a ha w hw φ hφ hc false
  have hz := actual_summable_norm T a ha w hw φ hφ hc true
  have hd := actual_signed_difference_summable T a ha w hw φ hφ hc
  have hK : 0 ≤ 7 * Real.pi / 9 := by positivity
  cases k with
  | ordinate => exact hr
  | weighted => exact bounded_kernel_summable_norm _ _ _ hK actualRationalKernel_bound hz
  | arguments => exact bounded_kernel_summable_norm _ _ _ hK actualRationalKernel_bound hd
  | horizontal =>
    apply bounded_kernel_summable_norm _ _ (7 * Real.pi / 9 + 7 * Real.pi / 9)
      (by positivity) _ hr
    intro t
    exact (norm_sub_le _ _).trans (add_le_add (actualRationalKernel_bound t) (actualRealKernel_bound t))
  | gaps =>
    apply bounded_kernel_summable_norm _ _ (7 * Real.pi / 9 + ‖kernelBenchmark‖)
      (by positivity) _ hr
    intro t
    exact (norm_sub_le _ _).trans (add_le_add (actualRealKernel_bound t) le_rfl)

theorem rationalTransferTerm_cutoff_limit (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (k : TransferTermKind) :
    Tendsto (fun N : Fin 3 → ℕ => ∑ t ∈ tripleDomain (fun j => occurrenceCutoff (N j)),
      rationalTransferTerm a w φ k t) atTop (𝓝 (∑' t, rationalTransferTerm a w φ k t)) :=
  independent_sequence_cutoff_limit (fun _ n => occurrenceCutoff n)
    (fun _ i => occurrenceCutoff_exhausts i) _ (rationalTransferTerm_summable T a ha w hw φ hφ hc k)

theorem rationalTransferSum_cutoff_limit (T : ℝ) (hT : 2*Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (k : TransferTermKind) :
    Tendsto (fun N : Fin 3 → ℕ =>
      (if k = .ordinate then ordinateCoefficient T else transferCoefficient T) *
      ∑ t ∈ tripleDomain (fun j => occurrenceCutoff (N j)),
        rationalTransferTerm (meanSpacing T) w φ k t) atTop (𝓝 (rationalTransferSum T w φ k)) :=
  (rationalTransferTerm_cutoff_limit T _ (meanSpacing_pos T hT) w hw φ hφ hc k).const_mul _

theorem rationalTransferTerm_telescope (a : ℝ) (w : ℝ → ℂ) (φ : ℝ × ℝ → ℂ)
    (t : Fin 3 → ZeroOccurrence) :
    rationalTransferTerm a w φ .weighted t =
      kernelBenchmark * rationalTransferTerm a w φ .ordinate t +
      rationalTransferTerm a w φ .arguments t + rationalTransferTerm a w φ .horizontal t +
      rationalTransferTerm a w φ .gaps t := by
  unfold rationalTransferTerm
  ring

theorem rationalTransfer_finite_telescope (a : ℝ) (w : ℝ → ℂ) (φ : ℝ × ℝ → ℂ)
    (D : Finset (Fin 3 → ZeroOccurrence)) :
    (∑ t ∈ D, rationalTransferTerm a w φ .weighted t) =
      kernelBenchmark * (∑ t ∈ D, rationalTransferTerm a w φ .ordinate t) +
      (∑ t ∈ D, rationalTransferTerm a w φ .arguments t) +
      (∑ t ∈ D, rationalTransferTerm a w φ .horizontal t) +
      (∑ t ∈ D, rationalTransferTerm a w φ .gaps t) := by
  simp_rw [rationalTransferTerm_telescope a w φ, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem rationalTransfer_tsum_telescope (T a : ℝ) (ha : 0 < a) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∑' t, rationalTransferTerm a w φ .weighted t) =
      kernelBenchmark * (∑' t, rationalTransferTerm a w φ .ordinate t) +
      (∑' t, rationalTransferTerm a w φ .arguments t) +
      (∑' t, rationalTransferTerm a w φ .horizontal t) +
      (∑' t, rationalTransferTerm a w φ .gaps t) := by
  have hs (k) := (rationalTransferTerm_summable T a ha w hw φ hφ hc k).of_norm
  simp_rw [rationalTransferTerm_telescope a w φ]
  rw [Summable.tsum_add (((hs .ordinate).mul_left kernelBenchmark).add (hs .arguments) |>.add (hs .horizontal)) (hs .gaps),
    Summable.tsum_add (((hs .ordinate).mul_left kernelBenchmark).add (hs .arguments)) (hs .horizontal),
    Summable.tsum_add ((hs .ordinate).mul_left kernelBenchmark) (hs .arguments), tsum_mul_left]

theorem scaledAnchorWeight_support (T : ℝ) (hT : 0 < T) (w : ℝ → ℂ)
    (hw : ∀ x, x ∉ Set.Ioo (1 : ℝ) 2 → w x = 0) :
    ∀ γ, γ ∉ Set.Icc T (2*T) → scaledAnchorWeight T w γ = 0 := by
  intro γ hγ
  apply hw
  intro h
  apply hγ
  exact ⟨(by simpa using ((lt_div_iff₀ hT).mp h.1).le),
    ((div_lt_iff₀ hT).mp h.2).le⟩

theorem scaledAnchorWeight_endpoints (T : ℝ) (hT : 0 < T) (w : ℝ → ℂ)
    (hw : ∀ x, x ∉ Set.Ioo (1 : ℝ) 2 → w x = 0) :
    scaledAnchorWeight T w T = 0 ∧ scaledAnchorWeight T w (2*T) = 0 := by
  have h₁ := hw 1 (by simp)
  have h₂ := hw 2 (by simp)
  simp [scaledAnchorWeight, hT.ne', h₁, h₂]

end
end HigherCorrelations
