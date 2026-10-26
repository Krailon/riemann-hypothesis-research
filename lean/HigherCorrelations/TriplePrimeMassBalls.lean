import HigherCorrelations.TripleArithmeticEnergy

/-! UNCONDITIONAL elementary coefficient-mass majorants. -/
namespace HigherCorrelations
noncomputable section

theorem triplePrimeMassRatio_range : 0<triplePrimeMassRatio ∧ triplePrimeMassRatio<1 := by
  have hs : 1<Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  unfold triplePrimeMassRatio
  exact ⟨by positivity,(div_lt_one (by positivity)).mpr hs⟩

theorem triplePrimeMass_geometric_summable :
    Summable (fun j : ℕ => triplePrimeMassRatio^j*(j+1:ℝ)) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := triplePrimeMassRatio)
    (by rw [Real.norm_eq_abs,abs_of_pos triplePrimeMassRatio_range.1]; exact triplePrimeMassRatio_range.2)
  have hg := summable_geometric_of_lt_one triplePrimeMassRatio_range.1.le triplePrimeMassRatio_range.2
  convert h.add hg using 1
  funext j
  simp only [pow_one]
  ring

theorem triplePrimeMassConstant_pos : 0<triplePrimeMassConstant := by
  have h : 0≤∑' j : ℕ, triplePrimeMassRatio^j*(j+1:ℝ) := tsum_nonneg (fun j => by positivity [triplePrimeMassRatio_range.1])
  unfold triplePrimeMassConstant
  linarith

theorem triplePrimeMassBall_nonneg (x : ℝ) (hx : 1≤x) (j n : ℕ) :
    0≤triplePrimeMassBall x j n := by
  have hl : 0≤Real.log (2*x) := Real.log_nonneg (by linarith)
  exact tripleNatBall_nonneg _ _ (by positivity) n

theorem triplePrimeMassBall_bound (x : ℝ) (hx : 1≤x) (j : ℕ) :
    (∑' n, triplePrimeMassBall x j n) ≤
      (2*Real.sqrt x*Real.log (2*x))*(triplePrimeMassRatio^j*(j+1:ℝ)) := by
  have hx0 : 0<x := by linarith
  have hl : 0≤Real.log (2*x) := Real.log_nonneg (by linarith)
  have hs : Real.sqrt x≠0 := (Real.sqrt_pos.mpr hx0).ne'
  apply (tripleNatBall_bound _ _ (by positivity) (by positivity)).trans
  apply le_of_eq
  have he : (2:ℝ)^j*(1/(2*Real.sqrt 2):ℝ)^j = triplePrimeMassRatio^j := by
    rw [← mul_pow]
    congr 1
    unfold triplePrimeMassRatio
    field_simp
  rw [pow_succ]
  calc
    _ = (2*x/Real.sqrt x*Real.log (2*x))*((2:ℝ)^j*(1/(2*Real.sqrt 2):ℝ)^j)*(j+1:ℝ) := by ring
    _ = _ := by
      rw [he,mul_div_assoc,show x/Real.sqrt x=Real.sqrt x from by
        apply (div_eq_iff hs).mpr; nlinarith [Real.sq_sqrt hx0.le]]
      ring

theorem triplePrimeMassBall_double_summable (x : ℝ) (hx : 1≤x) :
    Summable (fun p : ℕ × ℕ => triplePrimeMassBall x p.1 p.2) := by
  have hnon (p : ℕ × ℕ) := triplePrimeMassBall_nonneg x hx p.1 p.2
  have hr : Summable (fun j => ∑' n, triplePrimeMassBall x j n) :=
    Summable.of_nonneg_of_le (fun j => tsum_nonneg (triplePrimeMassBall_nonneg x hx j))
      (triplePrimeMassBall_bound x hx) (triplePrimeMass_geometric_summable.mul_left _)
  have hn (j : ℕ) : Summable (fun n => triplePrimeMassBall x j n) := by
    unfold triplePrimeMassBall
    exact tripleNatBall_summable _ _
  exact (summable_prod_of_nonneg hnon).mpr ⟨hn,hr⟩

end
end HigherCorrelations
