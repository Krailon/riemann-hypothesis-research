import HigherCorrelations.PairSieveAverage

/-! UNCONDITIONAL. Explicit cutoff and error absorption. Constants are deliberately
loose and effective; no unspecified asymptotic threshold is used. -/
namespace HigherCorrelations
noncomputable section
open Finset OAI.Problem337

theorem pairSievePrimeConstant_pos : 0 < pairSievePrimeConstant := by
  norm_num [pairSievePrimeConstant]

/-- The harmonic square converts the finite sieve into a logarithm-weighted
bound at any positive integer cutoff. -/
theorem pairSieve_cutoff_bound (U h N : ℕ) (hh : 2 ∣ h) (hh0 : h ≠ 0) (hN : 1 ≤ N) :
    ((pairSievePrimes U h).card : ℝ)*Real.log N^2 ≤ pairSieveBadFactor h*U +
      ((N : ℝ)^4*(1+2*Real.log N)^4+2*(N : ℝ)^2)*Real.log N^2 := by
  let D := GoldbachSelberg.denominator h (primorial (N^2)) (N^2)
  have hN2 : 1 ≤ N^2 := Nat.one_le_pow _ _ hN
  have hD : 0 < D := GoldbachSelberg.denominator_pos h _ hh (squarefree_primorial _) hN2
  have he := pairSieve_primes_le_primorial U h hh (z := N^2) hN2
  have hl := pairSieve_denominator_lower h N hh hh0 hN
  have hc : ((Nat.primesLE (N^2)).card : ℝ) ≤ (N : ℝ)^2 := by
    have hs : Nat.primesLE (N^2) ⊆ Icc 1 (N^2) := by
      intro p hp; exact mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, (Nat.mem_primesLE.mp hp).1⟩
    have hc := card_le_card hs
    simpa using (Nat.cast_le (α := ℝ)).mpr hc
  have hquot : ((U : ℝ)/D)*Real.log N^2 ≤ pairSieveBadFactor h*U := by
    have hg : Real.log N^2/D ≤ pairSieveBadFactor h := (div_le_iff₀ hD).mpr hl
    have hm := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg U : (0 : ℝ) ≤ U)
    convert hm using 1 <;> ring
  have he' := mul_le_mul_of_nonneg_right he (sq_nonneg (Real.log N))
  simp only [Nat.cast_pow, Real.log_pow] at he'
  norm_num only [Nat.cast_ofNat] at he'
  have hpow : ((N : ℝ)^2)^2 = (N : ℝ)^4 := by ring
  rw [hpow] at he'
  have hcorr := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log N))
  dsimp [D] at hquot
  nlinarith

/-- A floor eighth-root cutoff, with a quantitative lower bound for its log. -/
theorem pairSieve_cutoff_parameters (U : ℝ) (hU : 1 ≤ U) (hlog : 16 ≤ Real.log U) :
    let N := ⌊U^(1/8:ℝ)⌋₊
    1 ≤ N ∧ (N : ℝ) ≤ U^(1/8:ℝ) ∧ Real.log U ≤ 16*Real.log N := by
  let y := U^(1/16:ℝ)
  let x := U^(1/8:ℝ)
  let N := ⌊x⌋₊
  have hU0 : 0 < U := by linarith
  have hy : 2 ≤ y := by
    have he : 1 ≤ Real.log U * (1/16:ℝ) := by linarith
    have ha := Real.add_one_le_exp (Real.log U * (1/16:ℝ))
    rw [← Real.rpow_def_of_pos hU0] at ha
    dsimp [y]; linarith
  have hy2 : y^2 = x := by
    dsimp [y, x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    norm_num
  have hx0 : 0 ≤ x := Real.rpow_nonneg hU0.le _
  have hnlo : x < (N : ℝ)+1 := Nat.lt_floor_add_one x
  have hyN : y ≤ (N : ℝ) := by nlinarith
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  refine ⟨hN, Nat.floor_le hx0, ?_⟩
  have hlogs := Real.log_le_log (by linarith : 0 < y) hyN
  have hly : Real.log y = Real.log U/16 := by
    dsimp [y]; rw [Real.log_rpow hU0]; ring
  rw [hly] at hlogs
  linarith

/-- Explicit absorption of the logarithmic sieve error into the ambient height. -/
theorem pairSieve_error_absorb (U : ℝ) (hU : 1 ≤ U) (hlog : 1 ≤ Real.log U)
    (N : ℕ) (hN : 1 ≤ N) (hNU : (N : ℝ) ≤ U^(1/8:ℝ)) :
    ((N : ℝ)^4*(1+2*Real.log N)^4+2*(N : ℝ)^2)*Real.log N^2 ≤
      (81*16^6+512)*U := by
  have hU0 : 0 < U := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hNU' : (N : ℝ) ≤ U := hNU.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hU (show (1/8:ℝ) ≤ 1 by norm_num))
  have hlogs : Real.log N ≤ Real.log U := Real.log_le_log hN0 hNU'
  have hN4 : (N : ℝ)^4 ≤ U^(1/2:ℝ) := by
    have he := pow_le_pow_left₀ hN0.le hNU 4
    rw [← Real.rpow_natCast (U^(1/8:ℝ)), ← Real.rpow_mul hU0.le] at he
    norm_num at he
    exact he
  have hN2 : (N : ℝ)^2 ≤ U^(1/4:ℝ) := by
    have he := pow_le_pow_left₀ hN0.le hNU 2
    rw [← Real.rpow_natCast (U^(1/8:ℝ)), ← Real.rpow_mul hU0.le] at he
    norm_num at he
    exact he
  have hsmall : Real.log U ≤ 16*U^(1/16:ℝ) := by
    have := Real.log_le_rpow_div hU0.le (show (0 : ℝ)<1/16 by norm_num)
    linarith
  have hL6 : Real.log U^6 ≤ 16^6*U^(3/8:ℝ) := by
    have he := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log U) hsmall 6
    rw [mul_pow, ← Real.rpow_natCast (U^(1/16:ℝ)), ← Real.rpow_mul hU0.le] at he
    norm_num at he ⊢
    exact he
  have hL2 : Real.log U^2 ≤ 16^2*U^(1/8:ℝ) := by
    have he := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log U) hsmall 2
    rw [mul_pow, ← Real.rpow_natCast (U^(1/16:ℝ)), ← Real.rpow_mul hU0.le] at he
    norm_num at he ⊢
    exact he
  have hterm1 : (N : ℝ)^4*(1+2*Real.log N)^4*Real.log N^2 ≤ 81*16^6*U := by
    calc
      _ ≤ U^(1/2:ℝ)*(3*Real.log U)^4*Real.log U^2 := by gcongr <;> linarith
      _ = 81*U^(1/2:ℝ)*Real.log U^6 := by ring
      _ ≤ 81*U^(1/2:ℝ)*(16^6*U^(3/8:ℝ)) := by gcongr
      _ = (81*16^6)*U^(7/8:ℝ) := by
        rw [show (7/8:ℝ) = 1/2+3/8 by norm_num, Real.rpow_add hU0]; ring
      _ ≤ _ := by gcongr; simpa using Real.rpow_le_rpow_of_exponent_le hU (show (7/8:ℝ) ≤ 1 by norm_num)
  have hterm2 : 2*(N : ℝ)^2*Real.log N^2 ≤ 512*U := by
    calc
      _ ≤ 2*U^(1/4:ℝ)*Real.log U^2 := by gcongr
      _ ≤ 2*U^(1/4:ℝ)*(16^2*U^(1/8:ℝ)) := by gcongr
      _ = 512*U^(3/8:ℝ) := by
        rw [show (3/8:ℝ) = 1/4+1/8 by norm_num, Real.rpow_add hU0]; ring
      _ ≤ _ := by gcongr; simpa using Real.rpow_le_rpow_of_exponent_le hU (show (3/8:ℝ) ≤ 1 by norm_num)
  nlinarith

/-- A fully uniform even-shift prime-pair bound, with an absolute numerical
bound. Both primes need not be below U; the first coordinate is below U. -/
theorem pairSieve_prime_bound (U h : ℕ) (hU : 2 ≤ U) (hh : 2 ∣ h) (hh0 : h ≠ 0) :
    ((pairSievePrimes U h).card : ℝ)*Real.log U^2 ≤ pairSievePrimeConstant*pairSieveBadFactor h*U := by
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast (show 1 ≤ U by omega)
  have hlog0 := Real.log_nonneg hU1
  have hG := pairSieveBadFactor_one_le h
  by_cases hlog : 16 ≤ Real.log U
  · let N := ⌊(U : ℝ)^(1/8:ℝ)⌋₊
    obtain ⟨hN, hNU, hlogN⟩ := pairSieve_cutoff_parameters U hU1 hlog
    have he := pairSieve_cutoff_bound U h N hh hh0 hN
    have herr := pairSieve_error_absorb U hU1 (by linarith) N hN hNU
    have hsq : Real.log U^2 ≤ 256*Real.log N^2 := by
      have := sq_le_sq₀ hlog0 (by have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN); positivity)
      nlinarith [sq_nonneg (Real.log U-16*Real.log N)]
    have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (pairSievePrimes U h).card : (0 : ℝ) ≤ _)
    have hGU : (U : ℝ) ≤ pairSieveBadFactor h*U := by nlinarith
    unfold pairSievePrimeConstant
    nlinarith
  · have hc : ((pairSievePrimes U h).card : ℝ) ≤ U := by
      have := card_le_card (filter_subset (fun n => n.Prime ∧ (n+h).Prime) (Icc 1 U))
      simpa [pairSievePrimes] using (Nat.cast_le (α := ℝ)).mpr this
    have hsq : Real.log U^2 ≤ 256 := by nlinarith
    have hm := mul_le_mul hc hsq (sq_nonneg (Real.log U)) (Nat.cast_nonneg U)
    have hGU : (U : ℝ) ≤ pairSieveBadFactor h*U := by nlinarith
    unfold pairSievePrimeConstant
    nlinarith
end
end HigherCorrelations
