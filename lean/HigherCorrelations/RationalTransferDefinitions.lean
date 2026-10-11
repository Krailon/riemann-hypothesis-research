import HigherCorrelations.ActualCorrelationDefinitions

/-! Definition-only interface for the rational profile and signed transfer.
UNCONDITIONAL. The profile here is defined algebraically; its integral evaluation
is a separate obligation. All tuple sums retain both signs and multiplicities. -/
namespace HigherCorrelations
noncomputable section

def rationalKernel (z₁ z₂ z₃ : ℂ) : ℂ :=
  Real.pi * (24 + (z₁ - z₂)^2 + (z₁ - z₃)^2 + (z₂ - z₃)^2) /
    ((4 + (z₁ - z₂)^2) * (4 + (z₁ - z₃)^2) * (4 + (z₂ - z₃)^2))

def rationalProfile (a b e f g : ℝ) : ℂ :=
  rationalKernel ((a : ℂ) - Complex.I * e) ((b : ℂ) - Complex.I * f) (Complex.I * g)

def actualRationalKernel (t : Fin 3 → ZeroOccurrence) : ℂ :=
  rationalProfile (occurrenceOrdinate (t 1) - occurrenceOrdinate (t 0))
    (occurrenceOrdinate (t 2) - occurrenceOrdinate (t 0))
    (occurrenceDisplacement (t 1)) (occurrenceDisplacement (t 2))
    (occurrenceDisplacement (t 0))

def actualRealKernel (t : Fin 3 → ZeroOccurrence) : ℂ :=
  rationalProfile (occurrenceOrdinate (t 1) - occurrenceOrdinate (t 0))
    (occurrenceOrdinate (t 2) - occurrenceOrdinate (t 0)) 0 0 0

def kernelBenchmark : ℂ := 3 * Real.pi / 8
def transferCoefficient (T : ℝ) : ℂ := 16 / (3 * (T : ℂ) * Real.log T)
def ordinateCoefficient (T : ℝ) : ℂ := 1 / ((T : ℂ) * meanSpacing T)
def transferRatio (T : ℝ) : ℂ := (Real.log (T / (2 * Real.pi)) : ℂ) / Real.log T

inductive TransferTermKind where
  | ordinate | weighted | arguments | horizontal | gaps
  deriving DecidableEq

def rationalTransferTerm (a : ℝ) (w : ℝ → ℂ) (φ : ℝ × ℝ → ℂ)
    (k : TransferTermKind) (t : Fin 3 → ZeroOccurrence) : ℂ :=
  match k with
  | .ordinate => actualCorrelationTerm a w φ false t
  | .weighted => actualRationalKernel t * actualCorrelationTerm a w φ true t
  | .arguments => actualRationalKernel t *
      (actualCorrelationTerm a w φ true t - actualCorrelationTerm a w φ false t)
  | .horizontal => (actualRationalKernel t - actualRealKernel t) * actualCorrelationTerm a w φ false t
  | .gaps => (actualRealKernel t - kernelBenchmark) * actualCorrelationTerm a w φ false t

def rationalTransferSum (T : ℝ) (w : ℝ → ℂ) (φ : ℝ × ℝ → ℂ)
    (k : TransferTermKind) : ℂ :=
  (if k = .ordinate then ordinateCoefficient T else transferCoefficient T) *
    ∑' t, rationalTransferTerm (meanSpacing T) w φ k t

def scaledAnchorWeight (T : ℝ) (w : ℝ → ℂ) : ℝ → ℂ := fun γ => w (γ / T)

end
end HigherCorrelations
