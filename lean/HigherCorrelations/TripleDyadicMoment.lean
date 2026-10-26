import HigherCorrelations.TripleDyadicBalls

/-! UNCONDITIONAL logarithmic energy moments, with explicit convergent constants. -/
namespace HigherCorrelations
noncomputable section

theorem tripleMultiplicativeWeight_nonneg (x : ℝ) (hx : 0≤x) (n : ℕ) :
    0≤tripleMultiplicativeWeight x n := by unfold tripleMultiplicativeWeight; positivity

theorem tripleDyadicMoment_nonneg (x : ℝ) (k n : ℕ) : 0≤tripleDyadicMoment x k n := by
  by_cases hn : n=0
  · simp [hn,tripleDyadicMoment,tripleMultiplicativeWeight]
  · have hl : 0≤Real.log (2*n) := Real.log_nonneg (by exact_mod_cast (show 1≤2*n by omega))
    unfold tripleDyadicMoment
    positivity

theorem tripleDyadicMoment_head (x : ℝ) (hx : 1≤x) (k n : ℕ) (hn : (n:ℝ)≤x) :
    tripleDyadicMoment x k n ≤ tripleNatBall x (Real.log (2*x)^k) n := by
  by_cases hn0 : n=0
  · simp [hn0,tripleDyadicMoment,tripleMultiplicativeWeight,tripleNatBall]
  have hnp : 1≤n := by omega
  have hx0 : 0<x := by linarith
  have hl : 0≤Real.log (2*n) := Real.log_nonneg (by exact_mod_cast (show 1≤2*n by omega))
  have hw := (min_le_left ((n:ℝ)/x) (x/n)).trans ((div_le_one hx0).mpr hn)
  have hw0 := tripleMultiplicativeWeight_nonneg x hx0.le n
  have hpow : tripleMultiplicativeWeight x n^2 ≤ 1 := by
    unfold tripleMultiplicativeWeight at hw0 ⊢
    nlinarith
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<2*n) (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤2))
  simp only [tripleNatBall,hnp,hn,and_self,ite_true,tripleDyadicMoment]
  exact (mul_le_mul hpow (pow_le_pow_left₀ hl hlog k) (by positivity) (by norm_num)).trans_eq (one_mul _)

theorem tripleDyadicMoment_tail_cover (x : ℝ) (hx : 1≤x) (k n : ℕ) (hn : x<(n:ℝ)) :
    ∃ j : ℕ, tripleDyadicMoment x k n ≤ tripleDyadicBall x k j n := by
  have hx0 : 0<x := by linarith
  have hn0 : (0:ℝ)<n := hx0.trans hn
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near ((one_le_div hx0).mpr hn.le) (show (1:ℝ)<2 by norm_num)
  have hlo' : (2:ℝ)^j*x ≤ n := (le_div_iff₀ hx0).mp hlo
  have hhi' : (n:ℝ)≤(2:ℝ)^(j+1)*x := ((div_lt_iff₀ hx0).mp hhi).le
  have hp0 : 0<(2:ℝ)^j := by positivity
  have hl : 0≤Real.log (2*n) := Real.log_nonneg (by exact_mod_cast (show 1≤2*n by exact_mod_cast (by linarith : (1:ℝ)≤2*n)))
  have hlog : Real.log (2*n) ≤ (j+2:ℝ)*Real.log (2*x) := by
    have hb := Real.log_le_log (by positivity : (0:ℝ)<2*n) (mul_le_mul_of_nonneg_left hhi' (by norm_num : (0:ℝ)≤2))
    have he : 2*((2:ℝ)^(j+1)*x) = (2:ℝ)^(j+1)*(2*x) := by ring
    rw [he,Real.log_mul (by positivity : (2:ℝ)^(j+1)≠0) (by positivity : 2*x≠0),Real.log_pow] at hb
    have hll : Real.log 2≤Real.log (2*x) := Real.log_le_log (by norm_num) (by linarith)
    have hh := mul_le_mul_of_nonneg_left hll (show (0:ℝ)≤j+1 by positivity)
    norm_num only [Nat.cast_add,Nat.cast_one] at hb
    nlinarith
  have hw : tripleMultiplicativeWeight x n ≤ 1/(2:ℝ)^j :=
    (min_le_right _ _).trans ((div_le_div_iff₀ hn0 hp0).mpr (by simpa only [mul_comm,mul_one] using hlo'))
  have hw0 := tripleMultiplicativeWeight_nonneg x hx0.le n
  have hw2 : tripleMultiplicativeWeight x n^2 ≤ (1/4:ℝ)^j := by
    have h := pow_le_pow_left₀ hw0 hw 2
    convert h using 1
    simp only [div_pow,one_pow,← pow_mul]
    rw [mul_comm j 2,pow_mul]
    norm_num
  refine ⟨j,?_⟩
  have hn1 : 1≤n := by exact_mod_cast (show (0:ℝ)<n from hn0)
  simp only [tripleDyadicBall,tripleNatBall,hn1,hhi',and_self,ite_true,tripleDyadicMoment]
  exact mul_le_mul hw2 (pow_le_pow_left₀ hl hlog k) (by positivity) (by positivity)

theorem tripleDyadicMoment_majorant (x : ℝ) (hx : 1≤x) (k n : ℕ) :
    tripleDyadicMoment x k n ≤ tripleNatBall x (Real.log (2*x)^k) n +
      ∑' j, tripleDyadicBall x k j n := by
  have hl : 0≤Real.log (2*x) := Real.log_nonneg (by linarith)
  by_cases hn : (n:ℝ)≤x
  · exact (tripleDyadicMoment_head x hx k n hn).trans (le_add_of_nonneg_right
      (tsum_nonneg (fun j => tripleDyadicBall_nonneg x hx k j n)))
  · obtain ⟨j,hj⟩ := tripleDyadicMoment_tail_cover x hx k n (lt_of_not_ge hn)
    have h := hj.trans (((tripleDyadicBall_double_summable x hx k).prod_symm.prod_factor n).le_tsum j
      (fun i _ => tripleDyadicBall_nonneg x hx k i n))
    exact h.trans (le_add_of_nonneg_left (tripleNatBall_nonneg _ _ (by positivity) n))

theorem tripleDyadicMoment_summable (x : ℝ) (hx : 1≤x) (k : ℕ) :
    Summable (tripleDyadicMoment x k) :=
  Summable.of_nonneg_of_le (tripleDyadicMoment_nonneg x k) (tripleDyadicMoment_majorant x hx k)
    ((tripleNatBall_summable _ _).add (tripleDyadicBall_double_summable x hx k).prod_symm.prod)

theorem tripleDyadicMoment_bound (x : ℝ) (hx : 1≤x) (k : ℕ) :
    (∑' n, tripleDyadicMoment x k n) ≤ tripleDyadicConstant k*x*Real.log (2*x)^k := by
  have hl : 0≤Real.log (2*x) := Real.log_nonneg (by linarith)
  have hd := tripleDyadicBall_double_summable x hx k
  have hh := (tripleDyadicMoment_summable x hx k).tsum_le_tsum (tripleDyadicMoment_majorant x hx k)
    ((tripleNatBall_summable _ _).add hd.prod_symm.prod)
  have hdt : Summable (fun n => ∑' j, tripleDyadicBall x k j n) := hd.prod_symm.prod
  rw [Summable.tsum_add (tripleNatBall_summable x (Real.log (2*x)^k)) hdt,
    Summable.tsum_comm (f := fun (j n : ℕ) => tripleDyadicBall x k j n) hd] at hh
  have hb := hd.prod.tsum_le_tsum (tripleDyadicBall_bound x hx k)
    ((tripleDyadic_geometric_summable k).mul_left (2*x*Real.log (2*x)^k))
  rw [tsum_mul_left] at hb
  have hh0 := tripleNatBall_bound x (Real.log (2*x)^k) (by linarith) (by positivity)
  unfold tripleDyadicConstant
  nlinarith

end
end HigherCorrelations
