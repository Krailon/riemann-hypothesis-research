import HigherCorrelations.PairXiZeros
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Quantitative elementary bounds for the absolutely convergent Hadamard zero terms.
UNCONDITIONAL. These bounds alone do not yet give the contour-vanishing theorem. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem pairHadamard_far_bound (z a : ℂ) (R : ℝ) (hR : 0 < R)
    (hz : ‖z‖ ≤ R) (ha : 2*R < ‖a‖) :
    ‖1/(z-a)+1/a‖ ≤ 2*R*‖a‖⁻¹^2 := by
  have hap : 0 < ‖a‖ := by linarith
  have htri : ‖a‖ ≤ ‖z‖ + ‖z-a‖ := by
    have hb := norm_sub_le z (z-a)
    simpa using hb
  have hza : ‖a‖/2 ≤ ‖z-a‖ := by linarith
  have hzapos : 0 < ‖z-a‖ := by linarith
  have he : 1/(z-a)+1/a = z/(a*(z-a)) := by
    field_simp [norm_pos_iff.mp hap, norm_pos_iff.mp hzapos]
    ring
  rw [he, norm_div, norm_mul]
  calc
    _ ≤ R/(‖a‖*(‖a‖/2)) :=
      div_le_div₀ (by positivity) hz (by positivity)
        (mul_le_mul_of_nonneg_left hza hap.le)
    _ = _ := by field_simp

theorem pairHadamard_gap_bound (z a : ℂ) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hgap : ε ≤ |z.im-a.im|) (ha : r ≤ ‖a‖) :
    ‖1/(z-a)+1/a‖ ≤ 1/ε+1/r := by
  have hz : ε ≤ ‖z-a‖ := hgap.trans (by simpa using Complex.abs_im_le_norm (z-a))
  apply (norm_add_le _ _).trans
  simp only [norm_div, norm_one]
  exact add_le_add (one_div_le_one_div_of_le hε hz) (one_div_le_one_div_of_le hr ha)

theorem pairXi_radius_lower : ∃ r : ℝ, 0 < r ∧
    ∀ p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      r ≤ ‖Hadamard.divisorZeroIndex₀_val p‖ :=
  Hadamard.exists_r0_le_norm_divisorZeroIndex₀_val
    differentiable_riemannXi riemannXi_nontrivial

theorem pairXi_count_bound : ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R →
    (Nat.card {p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) //
      ‖Hadamard.divisorZeroIndex₀_val p‖ ≤ R} : ℝ) ≤
        (A*(1+2*R)^(3/2:ℝ)+B)/Real.log 2 := by
  obtain ⟨A,hA,hgrowth⟩ := riemannXi_entireOfOrderAtMost_one.exists_log_growth
    (τ := 3/2) (by norm_num) (by norm_num)
  refine ⟨A,|Real.log ‖meromorphicTrailingCoeffAt riemannXi 0‖|,hA,abs_nonneg _,fun R hR => ?_⟩
  apply (Hadamard.card_ball_le_divisorMassClosedBall₀ differentiable_riemannXi (by linarith)).trans
  have h := Hadamard.divisorMassClosedBall₀_le_of_growth differentiable_riemannXi hgrowth hR
  simpa [abs_of_nonneg (by linarith : 0 ≤ 2*R)] using h

theorem pairXi_zeroSum_bound (z : ℂ) (R ε r : ℝ) (hR : 0 < R)
    (hz : ‖z‖ ≤ R) (hε : 0 < ε) (hr : 0 < r)
    (hgap : ∀ p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      ε ≤ |z.im-(Hadamard.divisorZeroIndex₀_val p).im|)
    (hradius : ∀ p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      r ≤ ‖Hadamard.divisorZeroIndex₀_val p‖) :
    ‖∑' p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1/(z-Hadamard.divisorZeroIndex₀_val p)+1/Hadamard.divisorZeroIndex₀_val p)‖ ≤
      (Nat.card {p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) //
        ‖Hadamard.divisorZeroIndex₀_val p‖ ≤ 2*R} : ℝ)*(1/ε+1/r) +
      2*R*(∑' p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        ‖Hadamard.divisorZeroIndex₀_val p‖⁻¹^2) := by
  classical
  let ι := Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)
  let f : ι → ℂ := fun p => 1/(z-Hadamard.divisorZeroIndex₀_val p)+1/Hadamard.divisorZeroIndex₀_val p
  have hfin : Set.Finite {p : ι | ‖Hadamard.divisorZeroIndex₀_val p‖ ≤ 2*R} :=
    Hadamard.divisorZeroIndex₀_norm_le_finite (2*R) (by simp)
  let S : Finset ι := hfin.toFinset
  let b : ι → ℝ := fun p => if p ∈ S then 1/ε+1/r else 0
  have hb : Summable b := summable_of_ne_finset_zero (s := S) (by intro p hp; simp [b,hp])
  have hf : Summable f := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (by
    intro p he
    have hg := hgap p
    rw [he, sub_self, abs_zero] at hg
    linarith)
  have hp (p : ι) : ‖f p‖ ≤ b p + 2*R*‖Hadamard.divisorZeroIndex₀_val p‖⁻¹^2 := by
    by_cases hmem : p ∈ S
    · have hg := pairHadamard_gap_bound z _ ε r hε hr (hgap p) (hradius p)
      exact hg.trans (by simp only [b, ite_eq_left hmem]; exact le_add_of_nonneg_right (by positivity))
    · have hlarge : 2*R < ‖Hadamard.divisorZeroIndex₀_val p‖ := by
        simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] using hmem
      simpa [b,hmem,f] using pairHadamard_far_bound z _ R hR hz hlarge
  have hsum := summable_riemannXi_divisorZeroIndex₀_norm_inv_sq.mul_left (2*R)
  have he : ∑' p, b p = (S.card:ℝ)*(1/ε+1/r) := by
    rw [tsum_eq_sum (s := S) (by intro p hp; simp [b,hp])]
    simp [b, mul_add]
  have hcard : S.card = Nat.card {p : ι // ‖Hadamard.divisorZeroIndex₀_val p‖ ≤ 2*R} := by
    exact (Set.ncard_eq_toFinset_card _ hfin).symm
  calc
    ‖∑' p, f p‖ ≤ ∑' p, ‖f p‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' p, (b p + 2*R*‖Hadamard.divisorZeroIndex₀_val p‖⁻¹^2) :=
      Summable.tsum_le_tsum hp hf.norm (hb.add hsum)
    _ = _ := by rw [hb.tsum_add hsum, he, hcard, tsum_mul_left]

theorem pairXi_logDeriv_bound :
    ∃ D r A B Q : ℝ, 0 ≤ D ∧ 0 < r ∧ 0 < A ∧ 0 ≤ B ∧ 0 ≤ Q ∧
      ∀ (z : ℂ) (R ε : ℝ), 1 ≤ R → ‖z‖ ≤ R → 0 < ε →
        (∀ i : ZeroOccurrence, ε ≤ |z.im-occurrenceOrdinate i|) →
        ‖logDeriv riemannXi z‖ ≤ D +
          ((A*(1+4*R)^(3/2:ℝ)+B)/Real.log 2)*(1/ε+1/r) + 2*R*Q := by
  obtain ⟨P,hdeg,hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  obtain ⟨a,b,hP⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one
    (Polynomial.natDegree_le_of_degree_le hdeg)
  obtain ⟨r,hr,hradius⟩ := pairXi_radius_lower
  obtain ⟨A,B,hA,hB,hcount⟩ := pairXi_count_bound
  let Q : ℝ := ∑' p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
    ‖Hadamard.divisorZeroIndex₀_val p‖⁻¹^2
  refine ⟨‖a‖,r,A,B,Q,norm_nonneg _,hr,hA,hB,tsum_nonneg (fun _ => sq_nonneg _),
    fun z R ε hR hz hε hgap => ?_⟩
  have hg (p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
      ε ≤ |z.im-(Hadamard.divisorZeroIndex₀_val p).im| := pairXi_index_gap z.im ε hgap p
  have hn (p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
      z ≠ Hadamard.divisorZeroIndex₀_val p := by
    intro he
    have hh := hg p
    rw [he, sub_self, abs_zero] at hh
    linarith
  have he := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac hn
  rw [hP] at he
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, Polynomial.derivative_X, mul_one, add_zero, zero_add,
    Polynomial.eval_C] at he
  rw [he]
  have hb := pairXi_zeroSum_bound z R ε r (by linarith) hz hε hr hg hradius
  have hc := hcount (2*R) (by linarith)
  have hc' : (Nat.card {p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) //
        ‖Hadamard.divisorZeroIndex₀_val p‖ ≤ 2*R}:ℝ) ≤
      (A*(1+4*R)^(3/2:ℝ)+B)/Real.log 2 := by convert hc using 1 <;> ring
  calc
    _ ≤ ‖a‖ + ‖∑' p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1/(z-Hadamard.divisorZeroIndex₀_val p)+1/Hadamard.divisorZeroIndex₀_val p)‖ := norm_add_le _ _
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hc' (by positivity : 0 ≤ 1/ε+1/r)
      linarith

end
end HigherCorrelations
