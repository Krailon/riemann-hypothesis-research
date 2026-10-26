import HigherCorrelations.TripleArithmeticFourier
import HigherCorrelations.TriplePrimeResonance

/-! UNCONDITIONAL identification of the grouped cubic diagonal with the exact
prime-power resonance mass. All ordered factorizations, including repetitions,
are preserved by the product map. -/
namespace HigherCorrelations
noncomputable section

private def resonantPairEquiv : {v : PrimeTriple // triplePrimeResonant v} ≃ ℕ × ℕ where
  toFun v := (v.val 0,v.val 1)
  invFun p := ⟨![p.1,p.2,(p.1+1)*(p.2+1)-1],by
    change (p.1+1)*(p.2+1)=((p.1+1)*(p.2+1)-1)+1
    exact (Nat.sub_add_cancel (show 1≤(p.1+1)*(p.2+1) from Nat.mul_pos (Nat.succ_pos p.1) (Nat.succ_pos p.2))).symm⟩
  left_inv v := by
    apply Subtype.ext
    funext r
    fin_cases r
    · rfl
    · rfl
    · have h := v.property
      change (v.val 0+1)*(v.val 1+1)=v.val 2+1 at h
      change (v.val 0+1)*(v.val 1+1)-1=v.val 2
      omega
  right_inv p := rfl

theorem tripleArithmeticCoefficient_le_mass (x : ℝ) (hx : 1≤x) (n : ℕ) :
    tripleArithmeticCoefficient x n ≤ triplePrimeMass x := by
  rw [← tripleArithmeticCoefficient_mass x hx]
  exact (tripleArithmeticCoefficient_summable x hx).le_tsum n (fun m _ => tripleArithmeticCoefficient_nonneg x hx m)

theorem tripleArithmetic_resonance_summable (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun p : ℕ × ℕ => tripleArithmeticCoefficient X p.1*tripleArithmeticCoefficient Y p.2*
      tripleArithmeticCoefficient (X*Y) (p.1*p.2)) := by
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  apply Summable.of_nonneg_of_le
    (fun p : ℕ × ℕ => mul_nonneg (mul_nonneg (tripleArithmeticCoefficient_nonneg X hX p.1)
      (tripleArithmeticCoefficient_nonneg Y hY p.2)) (tripleArithmeticCoefficient_nonneg (X*Y) hz _))
    (fun p : ℕ × ℕ => mul_le_mul_of_nonneg_left (tripleArithmeticCoefficient_le_mass (X*Y) hz _)
      (mul_nonneg (tripleArithmeticCoefficient_nonneg X hX p.1) (tripleArithmeticCoefficient_nonneg Y hY p.2)))
  exact ((tripleArithmeticCoefficient_summable X hX).mul_of_nonneg
    (tripleArithmeticCoefficient_summable Y hY) (tripleArithmeticCoefficient_nonneg X hX)
    (tripleArithmeticCoefficient_nonneg Y hY)).mul_right _

theorem tripleArithmetic_resonance_sum (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    (∑' p : ℕ × ℕ, tripleArithmeticCoefficient X p.1*tripleArithmeticCoefficient Y p.2*
      tripleArithmeticCoefficient (X*Y) (p.1*p.2)) = triplePrimeResonantMass X Y := by
  have hs := tripleArithmetic_resonance_summable X Y hX hY
  rw [hs.tsum_prod]
  have h0 : (∑' n, tripleArithmeticCoefficient X 0*tripleArithmeticCoefficient Y n*
      tripleArithmeticCoefficient (X*Y) (0*n)) = 0 := by simp [tripleArithmeticCoefficient_zero]
  rw [hs.prod.tsum_eq_zero_add,h0,zero_add]
  have hi (m : ℕ) := (tripleArithmetic_resonance_summable X Y hX hY).prod_factor (m+1)
  have he (m : ℕ) : (∑' n, tripleArithmeticCoefficient X (m+1)*tripleArithmeticCoefficient Y n*
      tripleArithmeticCoefficient (X*Y) ((m+1)*n)) =
      ∑' n, tripleArithmeticCoefficient X (m+1)*tripleArithmeticCoefficient Y (n+1)*
        tripleArithmeticCoefficient (X*Y) ((m+1)*(n+1)) := by
    rw [(hi m).tsum_eq_zero_add]
    simp [tripleArithmeticCoefficient_zero]
  simp_rw [he]
  rw [← triplePrimeResonantMass_reindex X Y hX hY,← resonantPairEquiv.symm.tsum_eq]
  have hcoef (p : ℕ × ℕ) : triplePrimeCoefficient X Y (resonantPairEquiv.symm p).val =
      tripleArithmeticCoefficient X (p.1+1)*tripleArithmeticCoefficient Y (p.2+1)*
        tripleArithmeticCoefficient (X*Y) ((p.1+1)*(p.2+1)) := by
    unfold triplePrimeCoefficient
    change pairMeanPrimeCoefficient X p.1*pairMeanPrimeCoefficient Y p.2*
      pairMeanPrimeCoefficient (X*Y) ((p.1+1)*(p.2+1)-1)=_
    rw [← tripleArithmeticCoefficient_succ,← tripleArithmeticCoefficient_succ,
      ← tripleArithmeticCoefficient_succ,Nat.sub_add_cancel (show 1≤(p.1+1)*(p.2+1) from Nat.mul_pos (Nat.succ_pos p.1) (Nat.succ_pos p.2))]
  simp_rw [hcoef]
  exact ((tripleArithmetic_resonance_summable X Y hX hY).comp_injective
    (show Function.Injective (fun p : ℕ × ℕ => (p.1+1,p.2+1)) by
      intro p q h; exact Prod.ext (by have hh := congrArg Prod.fst h; dsimp at hh; omega)
        (by have hh := congrArg Prod.snd h; dsimp at hh; omega))).tsum_prod.symm

theorem tripleArithmeticConvolution_diagonal (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    (∑' r, tripleArithmeticConvolution X Y r*tripleArithmeticCoefficient (X*Y) r) =
      triplePrimeResonantMass X Y := by
  have h := (tripleArithmetic_resonance_summable X Y hX hY).hasSum.tsum_fiberwise
    (fun p : ℕ × ℕ => p.1*p.2)
  have he (r : ℕ) :
      (∑' p : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {r},
        tripleArithmeticCoefficient X p.val.1*tripleArithmeticCoefficient Y p.val.2*
          tripleArithmeticCoefficient (X*Y) (p.val.1*p.val.2)) =
      tripleArithmeticConvolution X Y r*tripleArithmeticCoefficient (X*Y) r := by
    have hp (p : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {r}) : p.val.1*p.val.2=r := p.property
    simp_rw [hp]
    rw [tsum_mul_right,← tripleArithmeticConvolution_fiber]
  simp_rw [he] at h
  rw [tripleArithmetic_resonance_sum X Y hX hY] at h
  exact h.tsum_eq

theorem tripleLogConvolution_diagonal (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    (∑' n, tripleLogConvolution X Y n*star (tripleLogCoefficient (X*Y) n)) =
      (triplePrimeResonantMass X Y:ℂ) := by
  simp only [tripleLogConvolution,tripleLogCoefficient,Complex.star_def,Complex.conj_ofReal,
    ← Complex.ofReal_mul,← Complex.ofReal_tsum]
  congr 1
  rw [tripleNat_tsum_ge_two (fun n => tripleArithmeticConvolution X Y n*tripleArithmeticCoefficient (X*Y) n)
    (by simp [tripleArithmeticCoefficient_zero]) (by simp [tripleArithmeticCoefficient_one]),
    tripleArithmeticConvolution_diagonal X Y hX hY]

end
end HigherCorrelations
