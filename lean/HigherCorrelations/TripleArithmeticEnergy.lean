import HigherCorrelations.TripleArithmeticDefinitions
import HigherCorrelations.TripleDyadicMoment
import HigherCorrelations.TriplePrimeFourier
import HigherCorrelations.TripleLogGap

/-! UNCONDITIONAL prime coefficient energy; no prime-pair theorem is used. -/
namespace HigherCorrelations
noncomputable section

theorem tripleArithmeticCoefficient_succ (x : ℝ) (n : ℕ) :
    tripleArithmeticCoefficient x (n+1) = pairMeanPrimeCoefficient x n := by
  simp only [tripleArithmeticCoefficient,tripleMultiplicativeWeight,pairMeanPrimeCoefficient_sqrt,
    Nat.cast_add,Nat.cast_one]

theorem tripleArithmeticCoefficient_nonneg (x : ℝ) (hx : 1≤x) (n : ℕ) :
    0≤tripleArithmeticCoefficient x n := by
  unfold tripleArithmeticCoefficient
  exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (tripleMultiplicativeWeight_nonneg x (by linarith) n)

theorem tripleArithmeticCoefficient_zero (x : ℝ) : tripleArithmeticCoefficient x 0 = 0 := by
  simp [tripleArithmeticCoefficient]

theorem tripleArithmeticCoefficient_one (x : ℝ) : tripleArithmeticCoefficient x 1 = 0 := by
  simp [tripleArithmeticCoefficient]

theorem tripleArithmeticCoefficient_summable (x : ℝ) (hx : 1≤x) :
    Summable (tripleArithmeticCoefficient x) := by
  apply (summable_nat_add_iff 1).mp
  simp only [tripleArithmeticCoefficient_succ]
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pairMeanPrimeCoefficient_nonneg x hx _)] using
    pairMeanPrimeCoefficient_summable x hx

theorem tripleLogCoefficient_mass_summable (x : ℝ) (hx : 1≤x) :
    Summable (fun n => ‖tripleLogCoefficient x n‖) := by
  have h := (tripleArithmeticCoefficient_summable x hx).comp_injective
    (show Function.Injective (fun n : LogGapIndex => n.val) from Subtype.val_injective)
  simpa only [Function.comp_def,tripleLogCoefficient,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (tripleArithmeticCoefficient_nonneg x hx _)] using h

theorem tripleLogCoefficient_energy_pointwise (x : ℝ) (hx : 1≤x) (n : LogGapIndex) :
    tripleLogEnergyTerm (tripleLogCoefficient x) n ≤ tripleDyadicMoment x 3 n.val := by
  have hn : (0:ℝ)<n.val := by exact_mod_cast (show 0<n.val from lt_of_lt_of_le (by norm_num) n.property)
  have hs : Real.sqrt n.val ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hl : 0≤Real.log (2*n.val) := Real.log_nonneg (by nlinarith [show (2:ℝ)≤n.val by exact_mod_cast n.property])
  have hb : ArithmeticFunction.vonMangoldt n.val ≤ Real.log (2*n.val) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn (by linarith))
  have he : tripleLogEnergyTerm (tripleLogCoefficient x) n =
      ArithmeticFunction.vonMangoldt n.val^2*tripleMultiplicativeWeight x n.val^2*Real.log (2*n.val) := by
    simp only [tripleLogEnergyTerm,tripleLogCoefficient,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      tripleArithmeticCoefficient,mul_pow,div_pow,Real.sq_sqrt hn.le]
    field_simp
  rw [he]
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg hb 2)
    (mul_nonneg (sq_nonneg (tripleMultiplicativeWeight x n.val)) hl)
  unfold tripleDyadicMoment
  nlinarith

theorem tripleLogCoefficient_energy_summable (x : ℝ) (hx : 1≤x) :
    Summable (tripleLogEnergyTerm (tripleLogCoefficient x)) := by
  have h := (tripleDyadicMoment_summable x hx 3).comp_injective
    (show Function.Injective (fun n : LogGapIndex => n.val) from Subtype.val_injective)
  exact Summable.of_nonneg_of_le (tripleLogEnergyTerm_nonneg _) (tripleLogCoefficient_energy_pointwise x hx) h

theorem tripleLogCoefficient_energy_bound (x : ℝ) (hx : 1≤x) :
    tripleLogEnergy (tripleLogCoefficient x) ≤ tripleDyadicConstant 3*x*Real.log (2*x)^3 := by
  have hd := tripleDyadicMoment_summable x hx 3
  have he := tripleLogCoefficient_energy_summable x hx
  calc
    _ ≤ ∑' n : LogGapIndex, tripleDyadicMoment x 3 n.val :=
      he.tsum_le_tsum (tripleLogCoefficient_energy_pointwise x hx) (hd.comp_injective Subtype.val_injective)
    _ ≤ ∑' n : ℕ, tripleDyadicMoment x 3 n :=
      Summable.tsum_subtype_le (tripleDyadicMoment x 3) {n : ℕ | 2≤n} (tripleDyadicMoment_nonneg x 3) hd
    _ ≤ _ := tripleDyadicMoment_bound x hx 3

end
end HigherCorrelations
