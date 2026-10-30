import HigherCorrelations.SignedSeriesConvergence
import HigherCorrelations.ZeroOccurrenceReflection

/-! UNCONDITIONAL reciprocal reflection of the full multiplicity-preserving series. -/
namespace HigherCorrelations
noncomputable section

theorem pairZeroTerm_reciprocal (i : ZeroOccurrence) (X t : ℝ) :
    pairZeroTerm (occurrenceReflection i) (X⁻¹,t) = star (pairZeroTerm i (X,t)) := by
  simp only [pairZeroTerm,occurrenceReflection_displacement,occurrenceReflection_ordinate,
    Real.log_inv,Complex.ofReal_neg,star_div₀,star_mul,star_ofNat,
    Complex.star_def,← Complex.exp_conj,map_add,map_pow,map_one,map_mul,
    Complex.conj_ofReal,Complex.conj_I,map_sub]
  rw [mul_comm (Complex.exp _) (2:ℂ)]
  congr 1
  · congr 1
    ring
  · ring

theorem pairZeroSeries_reciprocal (X t : ℝ) :
    pairZeroSeries (X⁻¹,t) = star (pairZeroSeries (X,t)) := by
  unfold pairZeroSeries
  rw [Complex.star_def,Complex.conj_tsum]
  have h := (occurrenceReflection_involutive.toPerm).tsum_eq (fun i => pairZeroTerm i (X⁻¹,t))
  rw [← h]
  apply tsum_congr
  intro i
  exact pairZeroTerm_reciprocal i X t

theorem pairZeroSeries_unit_real (t : ℝ) : (pairZeroSeries (1,t)).im=0 := by
  have h := pairZeroSeries_reciprocal 1 t
  norm_num only [inv_one] at h
  have hi := congrArg Complex.im h
  simp only [Complex.star_def,Complex.conj_im] at hi
  linarith

end
end HigherCorrelations
