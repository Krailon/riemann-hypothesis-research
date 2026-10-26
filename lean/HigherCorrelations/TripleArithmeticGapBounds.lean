import HigherCorrelations.TriplePrimeMassBound

/-! UNCONDITIONAL arithmetic logarithmic-gap budgets with explicit coefficient
masses and energies. Constants are independent of all smoothing parameters. -/
namespace HigherCorrelations
noncomputable section

theorem tripleLogCoefficient_mass_bound (x : ℝ) (hx : 1≤x) :
    tripleLogMass (tripleLogCoefficient x) ≤ triplePrimeMass x := by
  have h := Summable.tsum_subtype_le (tripleArithmeticCoefficient x) {n : ℕ | 2≤n}
    (tripleArithmeticCoefficient_nonneg x hx) (tripleArithmeticCoefficient_summable x hx)
  rw [tripleArithmeticCoefficient_mass x hx] at h
  simp only [tripleLogMass,tripleLogCoefficient,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (tripleArithmeticCoefficient_nonneg x hx _)]
  convert h using 1 <;> rfl

theorem tripleLogGapBound_mono (c d : LogGapIndex → ℂ) (B C E F : ℝ)
    (hb : tripleLogMass c≤B) (hc : tripleLogMass d≤C)
    (he : tripleLogEnergy c≤E) (hf : tripleLogEnergy d≤F) :
    tripleLogGapBound c d ≤ B*C/Real.log 2 +4*Real.sqrt 2*Real.sqrt (E*F) := by
  have hbn : 0≤tripleLogMass c := tsum_nonneg (fun _ => norm_nonneg _)
  have hcn : 0≤tripleLogMass d := tsum_nonneg (fun _ => norm_nonneg _)
  have hen : 0≤tripleLogEnergy c := tsum_nonneg (tripleLogEnergyTerm_nonneg c)
  have hfn : 0≤tripleLogEnergy d := tsum_nonneg (tripleLogEnergyTerm_nonneg d)
  exact add_le_add
    (div_le_div_of_nonneg_right (mul_le_mul hb hc hcn (hbn.trans hb)) (Real.log_nonneg (by norm_num)))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul he hf hfn (hen.trans he))) (by positivity))

theorem tripleLogGap_mixed_budget (x y : ℝ) (hx : 1≤x) (hy : 1≤y) :
    tripleLogGapBound (tripleLogCoefficient x) (tripleLogCoefficient y) ≤
      (triplePrimeMassConstant*Real.sqrt x*Real.log (2*x))*
        (triplePrimeMassConstant*Real.sqrt y*Real.log (2*y))/Real.log 2 +
      4*Real.sqrt 2*Real.sqrt ((tripleDyadicConstant 3*x*Real.log (2*x)^3)*
        (tripleDyadicConstant 3*y*Real.log (2*y)^3)) :=
  tripleLogGapBound_mono _ _ _ _ _ _
    ((tripleLogCoefficient_mass_bound x hx).trans (triplePrimeMass_bound x hx))
    ((tripleLogCoefficient_mass_bound y hy).trans (triplePrimeMass_bound y hy))
    (tripleLogCoefficient_energy_bound x hx) (tripleLogCoefficient_energy_bound y hy)

theorem tripleLogGap_cubic_budget (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    tripleLogGapBound (tripleLogConvolution X Y) (tripleLogCoefficient (X*Y)) ≤
      ((triplePrimeMassConstant*Real.sqrt X*Real.log (2*X))*
        (triplePrimeMassConstant*Real.sqrt Y*Real.log (2*Y)))*
        (triplePrimeMassConstant*Real.sqrt (X*Y)*Real.log (2*(X*Y)))/Real.log 2 +
      4*Real.sqrt 2*Real.sqrt ((tripleDyadicConstant 5*(X*Y)*Real.log (2*(X*Y))^5)*
        (tripleDyadicConstant 3*(X*Y)*Real.log (2*(X*Y))^3)) := by
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  apply tripleLogGapBound_mono
  · exact (tripleLogConvolution_mass_bound X Y hX hY).trans
      (mul_le_mul (triplePrimeMass_bound X hX) (triplePrimeMass_bound Y hY)
        (tsum_nonneg (pairMeanPrimeCoefficient_nonneg Y hY))
        ((tsum_nonneg (pairMeanPrimeCoefficient_nonneg X hX)).trans (triplePrimeMass_bound X hX)))
  · exact (tripleLogCoefficient_mass_bound (X*Y) hz).trans (triplePrimeMass_bound (X*Y) hz)
  · exact tripleLogConvolution_energy_bound X Y hX hY
  · exact tripleLogCoefficient_energy_bound (X*Y) hz

end
end HigherCorrelations
