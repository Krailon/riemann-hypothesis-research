import HigherCorrelations.TripleResonanceDecay

/-! UNCONDITIONAL endpoint checks: either unit scale, product one, prime squares
and inclusive integer ball cutoffs. Repeated ordered factors remain present. -/
namespace HigherCorrelations
noncomputable section

theorem triplePrimeResonantMass_decay_unit_left (Y : ℝ) (hY : 1 ≤ Y) :
    0 ≤ triplePrimeResonantMass 1 Y ∧ triplePrimeResonantMass 1 Y ≤
      tripleResonanceDecayConstant*(Real.log (2*Y)^3/Real.sqrt Y) := by
  simpa only [one_mul] using triplePrimeResonantMass_decay 1 Y (by norm_num) hY

theorem triplePrimeResonantMass_decay_unit_right (X : ℝ) (hX : 1 ≤ X) :
    0 ≤ triplePrimeResonantMass X 1 ∧ triplePrimeResonantMass X 1 ≤
      tripleResonanceDecayConstant*(Real.log (2*X)^3/Real.sqrt X) := by
  simpa only [mul_one] using triplePrimeResonantMass_decay X 1 hX (by norm_num)

theorem triplePrimeResonantMass_decay_unit_unit :
    0 ≤ triplePrimeResonantMass 1 1 ∧ triplePrimeResonantMass 1 1 ≤
      tripleResonanceDecayConstant*Real.log 2^3 := by
  simpa using triplePrimeResonantMass_decay 1 1 (by norm_num) (by norm_num)

theorem tripleResonanceBall_integer_cutoff (Z : ℝ) (N n : ℕ) :
    tripleResonanceBall Z N n =
      if n ≤ N ∧ IsPrimePow n ∧ ¬n.Prime then (8*Z^2/(N:ℝ)^3)*Real.log (2*N)^3 else 0 := by
  simp only [tripleResonanceBall,Nat.floor_natCast]

theorem tripleResonanceBall_prime_square_endpoint (Z : ℝ) (p : ℕ) (hp : p.Prime) :
    tripleResonanceBall Z (p^2:ℕ) (p^2) =
      (8*Z^2/((p^2:ℕ):ℝ)^3)*Real.log (2*((p^2:ℕ):ℝ))^3 := by
  rw [tripleResonanceBall_integer_cutoff,if_pos]
  exact ⟨le_rfl,hp.isPrimePow.pow (by norm_num),Nat.Prime.not_prime_pow (by norm_num)⟩

/-- The p*p contribution is explicitly retained, including equal exponents. -/
theorem tripleResonance_square_summand (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (p : ℕ) (hp : p.Prime) :
    tripleArithmeticCoefficient X p*tripleArithmeticCoefficient Y p*
      tripleArithmeticCoefficient (X*Y) (p^2) ≤ tripleResonanceMajorant (X*Y) (p^2) := by
  have hZ : 1 ≤ X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hd : p ∈ (p^2).divisors := Nat.mem_divisors.mpr
    ⟨dvd_pow_self p (by norm_num),pow_ne_zero _ hp.ne_zero⟩
  have hs : tripleArithmeticCoefficient X p*tripleArithmeticCoefficient Y ((p^2)/p) ≤
      tripleArithmeticConvolution X Y (p^2) :=
    Finset.single_le_sum (fun d _ => mul_nonneg (tripleArithmeticCoefficient_nonneg X hX d)
      (tripleArithmeticCoefficient_nonneg Y hY _)) hd
  have he : p^2/p=p := by rw [pow_two,Nat.mul_div_cancel _ hp.pos]
  rw [he] at hs
  exact (mul_le_mul_of_nonneg_right hs (tripleArithmeticCoefficient_nonneg (X*Y) hZ _)).trans
    (tripleResonance_pointwise X Y hX hY _)

end
end HigherCorrelations
