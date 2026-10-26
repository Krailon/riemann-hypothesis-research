import HigherCorrelations.TripleBudgetUniformDefinitions
import HigherCorrelations.TripleBudgetPrimeNorm
import HigherCorrelations.TriplePrimeMassBound
import HigherCorrelations.TripleBudgetOffDiagonalRates

/-! UNCONDITIONAL primitive norm envelope with the closed x=2T branch.
The effective mass constant is evaluated exactly; the mean-square constant
remains the existential constant from the checked pair theorem. -/
namespace HigherCorrelations
noncomputable section

theorem triplePrimeMassConstant_closed :
    triplePrimeMassConstant = 1+2/(1-1/Real.sqrt 2)^2 := by
  have hr : ‖triplePrimeMassRatio‖<1 := by
    rw [Real.norm_eq_abs,abs_of_pos triplePrimeMassRatio_range.1]
    exact triplePrimeMassRatio_range.2
  have hh := tsum_choose_mul_geometric_of_norm_lt_one 1 hr
  have he : (∑' j : ℕ, triplePrimeMassRatio^j*(j+1:ℝ)) = 1/(1-triplePrimeMassRatio)^2 := by
    simpa [Nat.choose_one_right,mul_comm] using hh
  rw [triplePrimeMassConstant,he,triplePrimeMassRatio]
  ring

theorem tripleBudgetPrimeB_nonneg (x : ℝ) (hx : 1≤x) : 0≤tripleBudgetPrimeB x := by
  have hl : 0≤Real.log (2*x) := Real.log_nonneg (by linarith)
  unfold tripleBudgetPrimeB
  positivity [triplePrimeMassConstant_pos]

theorem tripleBudgetPrimeM_nonneg (C W T x : ℝ) (hx : 1≤x) : 0≤tripleBudgetPrimeM C W T x := by
  unfold tripleBudgetPrimeM
  split_ifs
  · exact le_min (tripleBudgetPrimeB_nonneg x hx) (Real.sqrt_nonneg _)
  · exact tripleBudgetPrimeB_nonneg x hx

theorem tripleBudgetPrimeM_endpoint (C W T : ℝ) :
    tripleBudgetPrimeM C W T (2*T) =
      min (tripleBudgetPrimeB (2*T)) (Real.sqrt (2*C*W*Real.log (4*T))) := by
  simp only [tripleBudgetPrimeM,le_refl,ite_true]
  congr 3 <;> ring

theorem tripleBudgetPrime_norm_envelope : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T x : ℝ,
      0≤W → (∀ u, ω u≤W) → 3≤T → 1≤x →
        tripleBudgetPrimeL2 ω T x ≤ tripleBudgetPrimeM C W T x := by
  obtain ⟨C,hC,hmean⟩ := tripleBudgetPrimeL2_uniform
  refine ⟨C,hC,?_⟩
  intro ω hω W T x hW hωW hT hx
  have hb := (tripleBudgetPrimeL2_mass ω hω T x hT hx).trans (triplePrimeMass_bound x hx)
  unfold tripleBudgetPrimeM
  split_ifs with h
  · exact le_min hb (hmean ω hω W T x hW hωW hT hx h)
  · exact hb

theorem tripleBudgetPrime_sup_envelope (x t : ℝ) (hx : 1≤x) :
    ‖pairPrimeSeries (x,t)‖≤tripleBudgetPrimeB x :=
  (tripleBudgetPrime_sup_mass x t hx).trans (triplePrimeMass_bound x hx)

end
end HigherCorrelations
