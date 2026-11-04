import HigherCorrelations.KernelLocalizationIdentity

/-! UNCONDITIONAL exact first stage of kernel localization. This interface
contains no tuplewise quantitative bound, summed error bound or height limit. -/
namespace HigherCorrelations
noncomputable section

theorem tripleKernelLocalizationError_zero (T : ℝ) (v : MasterTriple) :
    tripleKernelLocalizationError (fun _ => 0) T v=0 := by
  simp [tripleKernelLocalizationError,tripleKernelLocalizationIntegrand]

theorem tripleAnchoredProfile_repeated (i : ZeroOccurrence) :
    tripleAnchoredProfile (fun _ => i) = rationalProfile 0 0
      (occurrenceDisplacement i) (occurrenceDisplacement i) (occurrenceDisplacement i) := by
  simp [tripleAnchoredProfile]

end
end HigherCorrelations
