import HigherCorrelations.TripleArithmeticEnergy

/-! UNCONDITIONAL ordered product-frequency envelope and fifth logarithmic moment. -/
namespace HigherCorrelations
noncomputable section

theorem tripleMultiplicativeWeight_product (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (m n : ℕ) :
    tripleMultiplicativeWeight X m*tripleMultiplicativeWeight Y n ≤
      tripleMultiplicativeWeight (X*Y) (m*n) := by
  have hx := tripleMultiplicativeWeight_nonneg X (by linarith) m
  have hy := tripleMultiplicativeWeight_nonneg Y (by linarith) n
  unfold tripleMultiplicativeWeight at *
  rw [Nat.cast_mul]
  apply le_min
  · have h := mul_le_mul (min_le_left ((m:ℝ)/X) (X/m)) (min_le_left ((n:ℝ)/Y) (Y/n)) hy (by positivity : (0:ℝ) ≤ (m:ℝ)/X)
    simpa only [div_mul_div_comm] using h
  · have h := mul_le_mul (min_le_right ((m:ℝ)/X) (X/m)) (min_le_right ((n:ℝ)/Y) (Y/n)) hy (by positivity : (0:ℝ) ≤ X/(m:ℝ))
    simpa only [div_mul_div_comm] using h

theorem tripleArithmeticCoefficient_product (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (m n : ℕ) :
    tripleArithmeticCoefficient X m*tripleArithmeticCoefficient Y n ≤
      (ArithmeticFunction.vonMangoldt m*ArithmeticFunction.vonMangoldt n)/Real.sqrt (m*n) *
        tripleMultiplicativeWeight (X*Y) (m*n) := by
  have hp := mul_le_mul_of_nonneg_left (tripleMultiplicativeWeight_product X Y hX hY m n)
    (show 0≤(ArithmeticFunction.vonMangoldt m*ArithmeticFunction.vonMangoldt n)/Real.sqrt (m*n) by
      positivity [ArithmeticFunction.vonMangoldt_nonneg (n := m),ArithmeticFunction.vonMangoldt_nonneg (n := n)])
  convert hp using 1
  simp only [tripleArithmeticCoefficient,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg m)]
  ring

theorem tripleArithmeticConvolution_nonneg (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (r : ℕ) :
    0≤tripleArithmeticConvolution X Y r :=
  Finset.sum_nonneg (fun d _ => mul_nonneg (tripleArithmeticCoefficient_nonneg X hX d)
    (tripleArithmeticCoefficient_nonneg Y hY (r/d)))

theorem tripleArithmeticConvolution_bound (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (r : ℕ) (hr : 1≤r) :
    tripleArithmeticConvolution X Y r ≤
      tripleMultiplicativeWeight (X*Y) r*Real.log r^2/Real.sqrt r := by
  have hr0 : 0<r := by omega
  have hrR : (0:ℝ)<r := by exact_mod_cast hr0
  have hZ : 0≤X*Y := by positivity
  have hv := tripleMultiplicativeWeight_nonneg (X*Y) hZ r
  have hlog : 0≤Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  have hb (d : ℕ) (hd : d∈r.divisors) :
      tripleArithmeticCoefficient X d*tripleArithmeticCoefficient Y (r/d) ≤
        ArithmeticFunction.vonMangoldt d*Real.log r/Real.sqrt r*tripleMultiplicativeWeight (X*Y) r := by
    have hdvd := Nat.dvd_of_mem_divisors hd
    have he : d*(r/d)=r := Nat.mul_div_cancel' hdvd
    have hd0 : 0<d := Nat.pos_of_dvd_of_pos hdvd hr0
    have hq : 0<r/d := Nat.div_pos (Nat.le_of_dvd hr0 hdvd) hd0
    have hl : ArithmeticFunction.vonMangoldt (r/d) ≤ Real.log r :=
      ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast Nat.div_le_self r d))
    have hp := tripleArithmeticCoefficient_product X Y hX hY d (r/d)
    rw [← Nat.cast_mul,he] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)) hv)
  calc
    _ ≤ ∑ d ∈ r.divisors, ArithmeticFunction.vonMangoldt d*Real.log r/Real.sqrt r*tripleMultiplicativeWeight (X*Y) r :=
      Finset.sum_le_sum hb
    _ = _ := by
      simp only [← Finset.sum_mul,← Finset.sum_div,ArithmeticFunction.vonMangoldt_sum]
      ring

theorem tripleLogConvolution_energy_pointwise (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (n : LogGapIndex) :
    tripleLogEnergyTerm (tripleLogConvolution X Y) n ≤ tripleDyadicMoment (X*Y) 5 n.val := by
  have hn : (0:ℝ)<n.val := by exact_mod_cast (show 0<n.val by have := n.property; omega)
  have hlog : 0≤Real.log n.val := Real.log_nonneg (by exact_mod_cast (show 1≤n.val by have := n.property; omega))
  have hlog2 : 0≤Real.log (2*n.val) := Real.log_nonneg (by nlinarith [show (2:ℝ)≤n.val by exact_mod_cast n.property])
  have hll : Real.log n.val≤Real.log (2*n.val) := Real.log_le_log hn (by linarith)
  have hv := tripleMultiplicativeWeight_nonneg (X*Y) (by positivity) n.val
  have hb := tripleArithmeticConvolution_bound X Y hX hY n.val (by have := n.property; omega)
  have hb0 := tripleArithmeticConvolution_nonneg X Y hX hY n.val
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb 2)
    (mul_nonneg hn.le hlog2)
  simp only [div_pow,mul_pow,Real.sq_sqrt hn.le] at hh
  have he : (n.val:ℝ)*Real.log (2*n.val) *
      (tripleMultiplicativeWeight (X*Y) n.val^2*(Real.log n.val^2)^2/n.val) =
      tripleMultiplicativeWeight (X*Y) n.val^2*Real.log n.val^4*Real.log (2*n.val) := by
    field_simp
  rw [he] at hh
  have hpower := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hll 4)
    (mul_nonneg (sq_nonneg (tripleMultiplicativeWeight (X*Y) n.val)) hlog2)
  simp only [tripleLogEnergyTerm,tripleLogConvolution,Complex.norm_real,Real.norm_eq_abs,sq_abs,tripleDyadicMoment]
  nlinarith

theorem tripleLogConvolution_energy_summable (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    Summable (tripleLogEnergyTerm (tripleLogConvolution X Y)) := by
  have hZ : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  exact Summable.of_nonneg_of_le (tripleLogEnergyTerm_nonneg _) (tripleLogConvolution_energy_pointwise X Y hX hY)
    ((tripleDyadicMoment_summable (X*Y) hZ 5).comp_injective Subtype.val_injective)

theorem tripleLogConvolution_energy_bound (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    tripleLogEnergy (tripleLogConvolution X Y) ≤ tripleDyadicConstant 5*(X*Y)*Real.log (2*(X*Y))^5 := by
  have hZ : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hd := tripleDyadicMoment_summable (X*Y) hZ 5
  calc
    _ ≤ ∑' n : LogGapIndex, tripleDyadicMoment (X*Y) 5 n.val :=
      (tripleLogConvolution_energy_summable X Y hX hY).tsum_le_tsum (tripleLogConvolution_energy_pointwise X Y hX hY)
        (hd.comp_injective Subtype.val_injective)
    _ ≤ ∑' n : ℕ, tripleDyadicMoment (X*Y) 5 n :=
      Summable.tsum_subtype_le _ {n : ℕ | 2≤n} (tripleDyadicMoment_nonneg (X*Y) 5) hd
    _ ≤ _ := tripleDyadicMoment_bound (X*Y) hZ 5

end
end HigherCorrelations
