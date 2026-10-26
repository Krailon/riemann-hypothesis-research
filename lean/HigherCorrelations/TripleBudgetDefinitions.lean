import HigherCorrelations.TriplePrimeResonanceDefinitions
import HigherCorrelations.FourierDecayDefinitions

/-! UNCONDITIONAL definition-only interface for the signed triple budget.
The retained expression is exact; its definition asserts no asymptotic estimate.
Prime indices n represent n+1, including the zero coefficient at integer one. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

structure TripleBudgetWeight (ω : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ω
  support : tsupport ω ⊆ Ioo (1:ℝ) 2
  nonneg : ∀ u, 0 ≤ ω u
  mass : (∫ u : ℝ, ω u) = 1

def tripleBudgetMoment (ω : ℝ → ℝ) (T : ℝ) (r : ℕ) : ℝ :=
  ∫ u : ℝ, ω u * Real.log (|T*u|+2)^r

def tripleBudgetDiagonal (X Y : ℝ) : ℝ :=
  ∑' n : ℕ, pairMeanPrimeCoefficient X n * pairMeanPrimeCoefficient Y n

def tripleBudgetRetained (ω : ℝ → ℝ) (T X Y : ℝ) : ℂ :=
  (Real.log T^3/(X*Y)^2 +
    tripleBudgetMoment ω T 1 * tripleBudgetDiagonal X (X*Y)/Y +
    tripleBudgetMoment ω T 1 * tripleBudgetDiagonal Y (X*Y)/X -
    triplePrimeResonantMass X Y : ℝ)

inductive TripleBudgetError where
  | archcube | PPA | PAA | APA | AAP | PAPoff | APPoff | PPPoff
  deriving DecidableEq, Repr

instance : Fintype TripleBudgetError :=
  ⟨{.archcube,.PPA,.PAA,.APA,.AAP,.PAPoff,.APPoff,.PPPoff}, by intro e; cases e <;> simp⟩

def tripleBudgetError (ω : ℝ → ℝ) (T X Y : ℝ) : TripleBudgetError → ℂ
  | .archcube => ((tripleBudgetMoment ω T 3-Real.log T^3)/(X*Y)^2 : ℝ)
  | .PPA => tripleWordIntegral ω T X Y ![.P,.P,.A]
  | .PAA => -tripleWordIntegral ω T X Y ![.P,.A,.A]
  | .APA => -tripleWordIntegral ω T X Y ![.A,.P,.A]
  | .AAP => -tripleWordIntegral ω T X Y ![.A,.A,.P]
  | .PAPoff => tripleWordIntegral ω T X Y ![.P,.A,.P] -
      (tripleBudgetMoment ω T 1 * tripleBudgetDiagonal X (X*Y)/Y : ℝ)
  | .APPoff => tripleWordIntegral ω T X Y ![.A,.P,.P] -
      (tripleBudgetMoment ω T 1 * tripleBudgetDiagonal Y (X*Y)/X : ℝ)
  | .PPPoff => -tripleWordIntegral ω T X Y ![.P,.P,.P] + (triplePrimeResonantMass X Y : ℝ)

def tripleBudgetRemainderWords : Finset MasterWord :=
  Finset.univ.filter (fun w => tripleWordHasH w = true)

def tripleBudgetWordError (ω : ℝ → ℝ) (T X Y : ℝ) (w : MasterWord) : ℂ :=
  (tripleWordSign w:ℂ)*tripleWordIntegral ω T X Y w

abbrev TripleBudgetAssignment (w : MasterWord) := {r : Fin 3 // w r = .H} → PairRemainderKind

def tripleBudgetRefinedComponent (w : MasterWord) (κ : TripleBudgetAssignment w)
    (r : Fin 3) (x t : ℝ) : ℂ :=
  if h : w r = .H then pairRHSRemainder (κ ⟨r,h⟩) x t else tripleComponent (w r) x t

def tripleBudgetRefinedError (ω : ℝ → ℝ) (T X Y : ℝ) (w : MasterWord)
    (κ : TripleBudgetAssignment w) : ℂ :=
  (tripleWordSign w:ℂ)*tripleSmoothedIntegral ω T
    (tripleBudgetRefinedComponent w κ 0 X)
    (tripleBudgetRefinedComponent w κ 1 Y)
    (tripleBudgetRefinedComponent w κ 2 (X*Y))

def tripleBudgetEnvelope (ε Winf W₁ T : ℝ) : ℝ :=
  (1+Winf+W₁)*T^(-ε)*Real.log (2*T+2)^4

def tripleBudgetRemainderBound (j : PairRemainderKind) (T x : ℝ) : ℝ := match j with
  | .arch => pairArchConstant/x
  | .ds => pairDSConstant/x
  | .pole => 4*Real.sqrt x/(1+T^2)
  | .trivial => 12*x^(-5/2:ℝ)/(T+2)

def tripleBudgetRemainderTotal (T x : ℝ) : ℝ := ∑ j, tripleBudgetRemainderBound j T x

def tripleBudgetAlpha (T x : ℝ) : ℝ := Real.log (2*T+2)/x

def tripleBudgetPrimeL2 (ω : ℝ → ℝ) (T x : ℝ) : ℝ :=
  Real.sqrt (∫ t : ℝ, (ω (t/T)/T)*‖pairPrimeSeries (x,t)‖^2)

def tripleBudgetL2 (ω : ℝ → ℝ) (T : ℝ) (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (∫ t : ℝ, (ω (t/T)/T)*‖f t‖^2)

def tripleBudgetLetterNorm (ω : ℝ → ℝ) (T x : ℝ) : MasterLetter → ℝ
  | .P => tripleBudgetPrimeL2 ω T x
  | .A => tripleBudgetAlpha T x
  | .H => tripleBudgetRemainderTotal T x

def tripleBudgetRefinedNorm (ω : ℝ → ℝ) (T x : ℝ) (w : MasterWord)
    (κ : TripleBudgetAssignment w) (r : Fin 3) : ℝ :=
  if h : w r = .H then tripleBudgetRemainderBound (κ ⟨r,h⟩) T x
  else tripleBudgetLetterNorm ω T x (w r)

def tripleBudgetLogWeight (ω : ℝ → ℝ) (T : ℝ) (r : ℕ) (u : ℝ) : ℝ :=
  ω u*Real.log (T*u+2)^r

def tripleBudgetOmega (ω : ℝ → ℝ) (T : ℝ) (r : ℕ) : ℝ :=
  fourierDerivativeL1 (tripleBudgetLogWeight ω T r) 1

end
end HigherCorrelations
