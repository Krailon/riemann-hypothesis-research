import HigherCorrelations.TripleMasterDefinitions
import HigherCorrelations.PairRHSDefinitions

/-! UNCONDITIONAL definition-only interface for the ordered explicit-formula words.
H is the exact sum of four existing remainders. All integrals retain 1/T. -/
namespace HigherCorrelations
noncomputable section

inductive MasterLetter where
  | P | A | H
  deriving DecidableEq, Repr

instance : Fintype MasterLetter :=
  ⟨{.P,.A,.H}, by intro l; cases l <;> simp⟩

abbrev MasterWord := Fin 3 → MasterLetter

def tripleWordPrimeCount (w : MasterWord) : ℕ := ∑ r : Fin 3, if w r = .P then 1 else 0

def tripleWordSign (w : MasterWord) : ℤ := (-1)^tripleWordPrimeCount w

def tripleWordHasH (w : MasterWord) : Bool := decide (∃ r, w r = .H)

/-- The absolute value is essential for the all-real-t explicit formula. -/
def tripleArch (X t : ℝ) : ℂ := (Real.log (|t|+2)/X : ℝ)

def tripleComponent (l : MasterLetter) (X t : ℝ) : ℂ := match l with
  | .P => pairPrimeSeries (X,t)
  | .A => tripleArch X t
  | .H => pairRHSRemainderSum X t

def tripleSmoothedIntegrand (ω : ℝ → ℝ) (T : ℝ) (f g h : ℝ → ℂ) (t : ℝ) : ℂ :=
  (ω (t/T)/T : ℝ)*f t*g t*star (h t)

def tripleSmoothedIntegral (ω : ℝ → ℝ) (T : ℝ) (f g h : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, tripleSmoothedIntegrand ω T f g h t

def tripleWordIntegrand (ω : ℝ → ℝ) (T X Y : ℝ) (w : MasterWord) (t : ℝ) : ℂ :=
  tripleSmoothedIntegrand ω T (tripleComponent (w 0) X)
    (tripleComponent (w 1) Y) (tripleComponent (w 2) (X*Y)) t

def tripleWordIntegral (ω : ℝ → ℝ) (T X Y : ℝ) (w : MasterWord) : ℂ :=
  ∫ t : ℝ, tripleWordIntegrand ω T X Y w t

/-- The table is ordered lexicographically P,A,H, as in the manuscript.
Each row records (word, integer sign, contains-H flag). -/
def tripleWordTable : List (MasterWord × ℤ × Bool) := [
  (![.P,.P,.P], -1, false),
  (![.P,.P,.A], 1, false),
  (![.P,.P,.H], 1, true),
  (![.P,.A,.P], 1, false),
  (![.P,.A,.A], -1, false),
  (![.P,.A,.H], -1, true),
  (![.P,.H,.P], 1, true),
  (![.P,.H,.A], -1, true),
  (![.P,.H,.H], -1, true),
  (![.A,.P,.P], 1, false),
  (![.A,.P,.A], -1, false),
  (![.A,.P,.H], -1, true),
  (![.A,.A,.P], -1, false),
  (![.A,.A,.A], 1, false),
  (![.A,.A,.H], 1, true),
  (![.A,.H,.P], -1, true),
  (![.A,.H,.A], 1, true),
  (![.A,.H,.H], 1, true),
  (![.H,.P,.P], 1, true),
  (![.H,.P,.A], -1, true),
  (![.H,.P,.H], -1, true),
  (![.H,.A,.P], -1, true),
  (![.H,.A,.A], 1, true),
  (![.H,.A,.H], 1, true),
  (![.H,.H,.P], -1, true),
  (![.H,.H,.A], 1, true),
  (![.H,.H,.H], 1, true)]

end
end HigherCorrelations
