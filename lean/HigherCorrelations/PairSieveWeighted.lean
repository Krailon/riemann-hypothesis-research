import HigherCorrelations.PairSieveCover

/-! UNCONDITIONAL. PAIR-PRIME-COUNT-001: the weighted nearby-prime sieve bound
in the existing Fourier conventions. All tuples are ordered, all proper prime
powers remain, and the logarithmic cutoff is strict. -/
namespace HigherCorrelations
noncomputable section
set_option maxHeartbeats 400000

/-- Summability of the whole nonnegative dyadic covering family discharges
both orders of summation in the weighted argument. -/
theorem pairSieveBall_double_summable (X δ : ℝ) (hX : 1 ≤ X) (hδ : 0 ≤ δ) :
    Summable (fun q : ℕ × (ℕ × ℕ) => pairSieveBall X δ ((2:ℝ)^q.1*X) q.2) := by
  have hX0 : 0 < X := by linarith
  have hR (j : ℕ) : 0 ≤ (2:ℝ)^j*X := mul_nonneg (pow_nonneg (by norm_num) j) hX0.le
  have hnon (q : ℕ × (ℕ × ℕ)) : 0 ≤ pairSieveBall X δ ((2:ℝ)^q.1*X) q.2 :=
    pairSieveBall_nonneg X δ ((2:ℝ)^q.1*X) (hR q.1) q.2
  have hg : Summable (fun j : ℕ => ((pairSieveNearbyConstant/2)*δ*X)*(1/2:ℝ)^j) :=
    (summable_geometric_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (1/2:ℝ) < 1 by norm_num)).mul_left _
  have hr : Summable (fun j : ℕ => ∑' p : ℕ × ℕ, pairSieveBall X δ ((2:ℝ)^j*X) p) :=
    Summable.of_nonneg_of_le
      (fun j => tsum_nonneg (fun p => pairSieveBall_nonneg X δ ((2:ℝ)^j*X) (hR j) p))
      (fun j => pairSieveBall_dyadic_bound X δ hX0 hδ j) hg
  exact (summable_prod_of_nonneg hnon).mpr
    ⟨fun j => pairSieveBall_summable X δ ((2:ℝ)^j*X), hr⟩

/-- The actual prime coefficient product, with the strict nearby condition. -/
theorem pairSieve_weighted_summable (X δ : ℝ) (hX : 1 ≤ X) :
    Summable (fun p : ℕ × ℕ => if p.1 ≠ p.2 ∧
      |Real.log ((p.1+1:ℝ)/(p.2+1:ℝ))| < 2*Real.pi*δ then
      pairMeanPrimeCoefficient X p.1*pairMeanPrimeCoefficient X p.2 else 0) := by
  have hc : Summable (pairMeanPrimeCoefficient X) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pairMeanPrimeCoefficient_nonneg X hX _)] using pairMeanPrimeCoefficient_summable X hX
  apply Summable.of_nonneg_of_le _ _
    (hc.mul_of_nonneg hc (pairMeanPrimeCoefficient_nonneg X hX) (pairMeanPrimeCoefficient_nonneg X hX))
  · intro p; split_ifs
    · exact mul_nonneg (pairMeanPrimeCoefficient_nonneg X hX _) (pairMeanPrimeCoefficient_nonneg X hX _)
    · rfl
  · intro p; split_ifs
    · rfl
    · exact mul_nonneg (pairMeanPrimeCoefficient_nonneg X hX _) (pairMeanPrimeCoefficient_nonneg X hX _)

/-- Effective uniform weighted sieve bound, including X=1 and δ=1/2.
The additional endpoint δ=0 is valid because the nearby set is empty. -/
theorem pairMeanPrimeNearby_bound (X δ : ℝ) (hX : 1 ≤ X) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/2) :
    pairMeanPrimeNearby X δ ≤ pairSieveNearbyConstant*δ*X := by
  have hX0 : 0 < X := by linarith
  have hd := pairSieveBall_double_summable X δ hX hδ
  have hR (j : ℕ) : 0 ≤ (2:ℝ)^j*X := mul_nonneg (pow_nonneg (by norm_num) j) hX0.le
  have hg : Summable (fun j : ℕ => ((pairSieveNearbyConstant/2)*δ*X)*(1/2:ℝ)^j) :=
    (summable_geometric_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (1/2:ℝ) < 1 by norm_num)).mul_left _
  have hpoint : ∀ p : ℕ × ℕ, (if p.1 ≠ p.2 ∧
      |Real.log ((p.1+1:ℝ)/(p.2+1:ℝ))| < 2*Real.pi*δ then
      pairMeanPrimeCoefficient X p.1*pairMeanPrimeCoefficient X p.2 else 0) ≤
      ∑' j : ℕ, pairSieveBall X δ ((2:ℝ)^j*X) p := by
    intro p
    split_ifs with hp
    · obtain ⟨j,hj⟩ := pairSieveBall_cover X δ hX hδ hδhi p hp
      exact hj.trans ((hd.prod_symm.prod_factor p).le_tsum j
        (fun k _ => pairSieveBall_nonneg X δ ((2:ℝ)^k*X) (hR k) p))
    · exact tsum_nonneg (fun j => pairSieveBall_nonneg X δ ((2:ℝ)^j*X) (hR j) p)
  calc
    _ ≤ ∑' p : ℕ × ℕ, ∑' j : ℕ, pairSieveBall X δ ((2:ℝ)^j*X) p :=
      by
        exact (pairSieve_weighted_summable X δ hX).tsum_le_tsum hpoint hd.prod_symm.prod
    _ = ∑' j : ℕ, ∑' p : ℕ × ℕ, pairSieveBall X δ ((2:ℝ)^j*X) p := by
      exact Summable.tsum_comm (f := fun (j : ℕ) (p : ℕ × ℕ) =>
        pairSieveBall X δ ((2:ℝ)^j*X) p) hd
    _ ≤ ∑' j : ℕ, ((pairSieveNearbyConstant/2)*δ*X)*(1/2:ℝ)^j :=
      by
        exact hd.prod.tsum_le_tsum (fun j => pairSieveBall_dyadic_bound X δ hX0 hδ j) hg
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_two]
      ring

/-- Uniform constants are independent of X and δ; no sieve premise remains. -/
theorem pairMeanPrimeNearby_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ X δ : ℝ, 1 ≤ X → 0 < δ → δ ≤ 1/2 → pairMeanPrimeNearby X δ ≤ C*δ*X :=
  ⟨pairSieveNearbyConstant, pairSieveNearbyConstant_pos,
    fun X δ hX hδ hδhi => pairMeanPrimeNearby_bound X δ hX hδ.le hδhi⟩

end
end HigherCorrelations
