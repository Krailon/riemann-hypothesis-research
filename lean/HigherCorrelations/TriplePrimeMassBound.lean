import HigherCorrelations.TriplePrimeMassBalls
import HigherCorrelations.TripleConvolutionMass

/-! UNCONDITIONAL uniform prime mass O(sqrt(x) log(2x)), including x=1. -/
namespace HigherCorrelations
noncomputable section

theorem tripleArithmeticCoefficient_head (x R : ℝ) (hx : 0<x) (n : ℕ) (hn : (n:ℝ)≤R) :
    tripleArithmeticCoefficient x n ≤ ArithmeticFunction.vonMangoldt n*Real.sqrt R/x := by
  cases n with
  | zero => simp [tripleArithmeticCoefficient_zero]
  | succ n => simpa only [tripleArithmeticCoefficient_succ,Nat.cast_add,Nat.cast_one] using
      pairSieve_coefficient_head x R hx n (by simpa using hn)

theorem tripleArithmeticCoefficient_tail (x R : ℝ) (hx : 0<x) (hR : 0<R) (n : ℕ) (hn : R≤(n:ℝ)) :
    tripleArithmeticCoefficient x n ≤ ArithmeticFunction.vonMangoldt n*x/(R*Real.sqrt R) := by
  cases n with
  | zero => simp [tripleArithmeticCoefficient_zero]
  | succ n => simpa only [tripleArithmeticCoefficient_succ,Nat.cast_add,Nat.cast_one] using
      pairSieve_coefficient_tail x R hx hR n (by simpa using hn)

theorem triplePrimeMass_head (x : ℝ) (hx : 1≤x) (n : ℕ) (hn : (n:ℝ)≤x) :
    tripleArithmeticCoefficient x n ≤ tripleNatBall x (Real.log (2*x)/Real.sqrt x) n := by
  by_cases hn0 : n=0
  · simp [hn0,tripleArithmeticCoefficient_zero,tripleNatBall]
  have hn1 : 1≤n := by omega
  have hx0 : 0<x := by linarith
  have hs : Real.sqrt x≠0 := (Real.sqrt_pos.mpr hx0).ne'
  have hl : ArithmeticFunction.vonMangoldt n ≤ Real.log (2*x) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast (show 0<n by omega)) (by linarith))
  simp only [tripleNatBall,hn1,hn,and_self,ite_true]
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n*Real.sqrt x/x := tripleArithmeticCoefficient_head x x hx0 n hn
    _ ≤ Real.log (2*x)*Real.sqrt x/x := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hl (Real.sqrt_nonneg _)) hx0.le
    _ = _ := by field_simp; rw [Real.sq_sqrt hx0.le]; ring

theorem triplePrimeMass_tail_cover (x : ℝ) (hx : 1≤x) (n : ℕ) (hn : x<(n:ℝ)) :
    ∃ j : ℕ, tripleArithmeticCoefficient x n ≤ triplePrimeMassBall x j n := by
  have hx0 : 0<x := by linarith
  have hn0 : (0:ℝ)<n := hx0.trans hn
  have hn1 : 1≤n := by exact_mod_cast hn0
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near ((one_le_div hx0).mpr hn.le) (show (1:ℝ)<2 by norm_num)
  have hlo' : (2:ℝ)^j*x≤n := (le_div_iff₀ hx0).mp hlo
  have hhi' : (n:ℝ)≤(2:ℝ)^(j+1)*x := ((div_lt_iff₀ hx0).mp hhi).le
  have hlog : ArithmeticFunction.vonMangoldt n ≤ (j+1:ℝ)*Real.log (2*x) := by
    have h := ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hhi')
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx0.ne']
    rw [Real.log_mul (by positivity : (2:ℝ)^(j+1)≠0) hx0.ne',Real.log_pow] at h
    norm_num only [Nat.cast_add,Nat.cast_one] at h
    have hlx : 0≤Real.log x := Real.log_nonneg hx
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hlx]
  have hb := tripleArithmeticCoefficient_tail x ((2:ℝ)^j*x) hx0 (by positivity) n hlo'
  have hb' := hb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlog hx0.le) (by positivity))
  refine ⟨j,?_⟩
  simp only [triplePrimeMassBall,tripleNatBall,hn1,hhi',and_self,ite_true]
  convert hb' using 1
  have hsp : Real.sqrt ((2:ℝ)^j) = (Real.sqrt 2)^j := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [← pow_mul,mul_comm j 2,pow_mul,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [Real.sqrt_mul (by positivity : (0:ℝ)≤(2:ℝ)^j),hsp,one_div_pow,mul_pow]
  field_simp

theorem triplePrimeMass_bound (x : ℝ) (hx : 1≤x) :
    triplePrimeMass x ≤ triplePrimeMassConstant*Real.sqrt x*Real.log (2*x) := by
  have hx0 : 0<x := by linarith
  have hl : 0≤Real.log (2*x) := Real.log_nonneg (by linarith)
  have hd := triplePrimeMassBall_double_summable x hx
  have hdt : Summable (fun n => ∑' j, triplePrimeMassBall x j n) := hd.prod_symm.prod
  have hpoint (n : ℕ) : tripleArithmeticCoefficient x n ≤
      tripleNatBall x (Real.log (2*x)/Real.sqrt x) n + ∑' j, triplePrimeMassBall x j n := by
    by_cases hn : (n:ℝ)≤x
    · exact (triplePrimeMass_head x hx n hn).trans (le_add_of_nonneg_right
        (tsum_nonneg (fun j => triplePrimeMassBall_nonneg x hx j n)))
    · obtain ⟨j,hj⟩ := triplePrimeMass_tail_cover x hx n (lt_of_not_ge hn)
      exact (hj.trans ((hd.prod_symm.prod_factor n).le_tsum j (fun k _ => triplePrimeMassBall_nonneg x hx k n))).trans
        (le_add_of_nonneg_left (tripleNatBall_nonneg _ _ (by positivity) n))
  have h := (tripleArithmeticCoefficient_summable x hx).tsum_le_tsum hpoint
    ((tripleNatBall_summable _ _).add hdt)
  rw [tripleArithmeticCoefficient_mass x hx,
    Summable.tsum_add (tripleNatBall_summable x (Real.log (2*x)/Real.sqrt x)) hdt,
    Summable.tsum_comm (f := fun (j n : ℕ) => triplePrimeMassBall x j n) hd] at h
  have hb := hd.prod.tsum_le_tsum (triplePrimeMassBall_bound x hx)
    (triplePrimeMass_geometric_summable.mul_left _)
  rw [tsum_mul_left] at hb
  have hh := tripleNatBall_bound x (Real.log (2*x)/Real.sqrt x) hx0.le (by positivity)
  have he : x*(Real.log (2*x)/Real.sqrt x) = Real.sqrt x*Real.log (2*x) := by
    field_simp
    rw [Real.sq_sqrt hx0.le]
    ring
  rw [he] at hh
  unfold triplePrimeMassConstant
  nlinarith

end
end HigherCorrelations
