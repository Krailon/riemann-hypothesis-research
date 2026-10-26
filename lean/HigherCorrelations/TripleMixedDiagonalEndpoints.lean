import HigherCorrelations.TripleMixedDiagonalAsymptotic

/-! UNCONDITIONAL. Coincident knots, the unit scale, and integer cutoffs are
included. The integer identity applies in particular at every prime power. -/
namespace HigherCorrelations
noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt

theorem tripleMixedDiagonalWeight_self (a u : ℝ) :
    tripleMixedDiagonalWeight a a u = pairDiagonalWeight a u := by
  unfold tripleMixedDiagonalWeight pairDiagonalWeight
  split_ifs <;> ring

theorem tripleMixedDiagonalMain_self (a : ℝ) (ha : 1 ≤ a) :
    tripleMixedDiagonalMain a a = Real.log a := by
  have ha0 : a ≠ 0 := by linarith
  simp only [tripleMixedDiagonalMain, div_self ha0, Real.log_one, add_zero,
    mul_one, Real.log_mul ha0 ha0]
  field_simp
  <;> ring

theorem tripleMixedDiagonalModel_self (a : ℝ) (ha : 1 ≤ a) :
    tripleMixedDiagonalModel a a = Real.log a+1-1/(4*a^2) := by
  have ha0 : a ≠ 0 := by linarith
  rw [tripleMixedDiagonalModel,tripleMixedDiagonalMain_self a ha]
  simp only [div_self ha0, Real.log_one, add_zero, mul_one]
  ring

theorem tripleMixedDiagonal_unit_model (b : ℝ) :
    tripleMixedDiagonalModel 1 b =
      (1/(2*b))*(1+Real.log b)*Real.log b+(1/b)*(1+Real.log b)-1/(4*b) := by
  simp only [tripleMixedDiagonalModel,tripleMixedDiagonalMain,div_one,one_mul]
  ring

theorem tripleMixedDiagonal_unit_unit :
    tripleMixedDiagonalMain 1 1 = 0 ∧ tripleMixedDiagonalModel 1 1 = 3/4 := by
  norm_num [tripleMixedDiagonalMain,tripleMixedDiagonalModel]

/-- The equal-scale corollary is derived from the two-scale theorem. -/
theorem tripleMixedDiagonal_self_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 1 ≤ a →
    |pairMeanPrimeDiagonal a-Real.log a| ≤ C := by
  obtain ⟨C,hC,h⟩ := tripleMixedDiagonal_asymptotic
  refine ⟨C,hC,?_⟩
  intro a ha
  have he := h a a ha le_rfl
  change |tripleBudgetDiagonal a a-tripleMixedDiagonalMain a a| ≤ _ at he
  simpa only [tripleBudgetDiagonal_self,tripleMixedDiagonalMain_self a ha,
    div_self (show a ≠ 0 by linarith),Real.log_one,add_zero,mul_one] using he

theorem tripleMixedDiagonal_integer_split (A B N : ℕ) (hA : 1 ≤ A)
    (hAB : A ≤ B) (hBN : B ≤ N) :
    (∑ n ∈ Icc 0 N, tripleMixedDiagonalWeight A B n*(Λ n)^2) =
      (1/((A:ℝ)*B))*(∑ n ∈ Icc 0 A, (n:ℝ)*(Λ n)^2)+
      ((A:ℝ)/B)*(∑ n ∈ Ioc A B, (Λ n)^2/(n:ℝ))+
      ((A:ℝ)*B)*(∑ n ∈ Ioc B N, (Λ n)^2/(n:ℝ)^3) := by
  simpa only [Nat.floor_natCast] using tripleMixedDiagonal_finite_split A B N
    (by exact_mod_cast hA) (by exact_mod_cast hAB) (by exact_mod_cast hBN)

end
end HigherCorrelations
