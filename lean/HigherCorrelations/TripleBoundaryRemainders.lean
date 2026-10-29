import HigherCorrelations.TripleBudgetInteriorPrimitives
import HigherCorrelations.TripleBudgetInteriorErrors

/-! UNCONDITIONAL remainder bounds with all three inverse-scale factors retained.
The existing 208 component refinement identity is unchanged; the pole is
absorbed into the inverse-scale bound only in the proved range 1 <= x <= T. -/
namespace HigherCorrelations
noncomputable section

private def slotEnvelope (p a h x : ℝ) : MasterLetter → ℝ
  | .P => p
  | .A => a/x
  | .H => h/x

set_option maxHeartbeats 800000 in
private theorem remainder_polynomial (p a h X Y : ℝ) :
    (∑ w ∈ tripleBudgetRemainderWords,
      ∏ r : Fin 3, slotEnvelope p a h (![X,Y,X*Y] r) (w r)) =
    h*p^2*(1/X+1/Y+1/(X*Y)) +
    (2*a*h+h^2)*p*(1/(X*Y)+1/(X*(X*Y))+1/(Y*(X*Y))) +
    (3*a^2*h+3*a*h^2+h^3)/(X*Y*(X*Y)) := by
  have hf : tripleBudgetRemainderWords =
    {![.H,.P,.P],![.H,.P,.A],![.H,.P,.H],![.H,.A,.P],![.H,.A,.A],![.H,.A,.H],
     ![.H,.H,.P],![.H,.H,.A],![.H,.H,.H],![.P,.H,.P],![.P,.H,.A],![.P,.H,.H],
     ![.A,.H,.P],![.A,.H,.A],![.A,.H,.H],![.P,.P,.H],![.P,.A,.H],![.A,.P,.H],![.A,.A,.H]} := by decide
  rw [hf]
  norm_num [Fin.prod_univ_three,slotEnvelope]
  ring

theorem tripleBoundary_remainder_inverse (T x : ℝ) (hT : 3≤T)
    (hx : 1≤x) (hxT : x≤T) :
    tripleBudgetRemainderTotal T x ≤ tripleBudgetHConstant/x :=
  tripleBudget_remainder_interior T x x hT hx le_rfl hxT

theorem tripleBoundary_prime_height : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T x : ℝ,
    0≤W → (∀ u, ω u≤W) → 3≤T → 1≤x → x≤T →
    tripleBudgetPrimeL2 ω T x ≤ Real.sqrt (2*C*W*Real.log (2*T+2)) := by
  obtain ⟨C,hC,hmean⟩ := tripleBudgetPrimeL2_uniform
  refine ⟨C,hC,?_⟩
  intro ω hω W T x hW hωW hT hx hxT
  apply (hmean ω hω W T x hW hωW hT hx (by linarith)).trans
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left
    (tripleBudget_coefficient_log_height T x hT hx hxT).2 (by positivity)

theorem tripleBoundary_remainder_envelope : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T X Y : ℝ,
    0≤W → (∀ u, ω u≤W) → 3≤T → 1≤X → 1≤Y → X*Y≤T →
    let p := Real.sqrt (2*C*W*Real.log (2*T+2))
    let a := Real.log (2*T+2)
    let h := tripleBudgetHConstant
    (∑ w ∈ tripleBudgetRemainderWords, ‖tripleBudgetWordError ω T X Y w‖) ≤
    h*p^2*(1/X+1/Y+1/(X*Y)) +
    (2*a*h+h^2)*p*(1/(X*Y)+1/(X*(X*Y))+1/(Y*(X*Y))) +
    (3*a^2*h+3*a*h^2+h^3)/(X*Y*(X*Y)) := by
  obtain ⟨C,hC,hmean⟩ := tripleBoundary_prime_height
  refine ⟨C,hC,?_⟩
  intro ω hω W T X Y hW hωW hT hX hY hZT
  dsimp only
  rw [← remainder_polynomial]
  apply Finset.sum_le_sum
  intro w hw
  have hh := (Finset.mem_filter.mp hw).2
  apply (tripleBudget_word_bound ω hω T X Y hT hX hY w hh).trans
  have hz : 1≤X*Y := one_le_mul_of_one_le_of_one_le hX hY
  have hx (r : Fin 3) : 1≤(![X,Y,X*Y] r) := by fin_cases r <;> assumption
  have ht (r : Fin 3) : (![X,Y,X*Y] r)≤T := by
    fin_cases r
    · exact (show X≤X*Y by nlinarith).trans hZT
    · exact (show Y≤X*Y by nlinarith).trans hZT
    · exact hZT
  apply Finset.prod_le_prod₀
  · intro r _
    exact tripleBudgetLetterNorm_nonneg ω T _ hT (hx r) _
  · intro r _
    cases he : w r
    · exact hmean ω hω W T _ hW hωW hT (hx r) (ht r)
    · exact le_rfl
    · exact tripleBoundary_remainder_inverse T _ hT (hx r) (ht r)

set_option maxHeartbeats 800000 in
/-- A two-dimensional envelope that is integrable at the axis boundary layers.
The first term is used on the bounded transverse interval of the support. -/
theorem tripleBoundary_remainder_bound : ∃ K : ℝ, 0<K ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T X Y : ℝ,
    0≤W → (∀ u, ω u≤W) → 3≤T → 1≤X → 1≤Y → X*Y≤T →
    (∑ w ∈ tripleBudgetRemainderWords, ‖tripleBudgetWordError ω T X Y w‖) ≤
    K*(1+W)*(Real.log (2*T+2)*(1/X+1/Y)+Real.log (2*T+2)^2/(X*Y)) := by
  obtain ⟨C,hC,hbound⟩ := tripleBoundary_remainder_envelope
  let H := tripleBudgetHConstant
  let D := 2*C+1
  let A := 2*H*D
  let E := 3*(2*H+H^2)*D+(3*H+3*H^2+H^3)
  have hH : 0<H := tripleBudgetHConstant_pos
  have hD : 0<D := by dsimp [D]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hE : 0<E := by dsimp [E]; positivity
  refine ⟨A+E,by positivity,?_⟩
  intro ω hω W T X Y hW hωW hT hX hY hZT
  let L := Real.log (2*T+2)
  let V := 1+W
  let p := Real.sqrt (2*C*W*L)
  have hL : 1≤L := tripleBudget_height_log T hT
  have hV : 1≤V := by dsimp [V]; linarith
  have hp0 : 0≤p := Real.sqrt_nonneg _
  have hp2 : p^2=2*C*W*L := Real.sq_sqrt (by positivity)
  have hp2' : p^2≤D*V*L := by
    dsimp [D,V] at *
    nlinarith [mul_nonneg hC.le hW]
  have hp : p≤D*V*L := by
    have hk : 1≤D*V*L := by
      have hd : 1≤D := by dsimp [D]; linarith
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd hV) hL
    nlinarith [sq_nonneg (D*V*L-1)]
  have hx0 : 0<X := by linarith
  have hy0 : 0<Y := by linarith
  have hz : 1≤X*Y := one_le_mul_of_one_le_of_one_le hX hY
  have hz0 : 0<X*Y := by positivity
  have hxy : 1/(X*Y)≤1/X := one_div_le_one_div_of_le hx0 (by nlinarith)
  have hxx : 1/(X*(X*Y))≤1/(X*Y) := one_div_le_one_div_of_le hz0 (by nlinarith)
  have hyy : 1/(Y*(X*Y))≤1/(X*Y) := one_div_le_one_div_of_le hz0 (by nlinarith)
  have hzz : 1/(X*Y*(X*Y))≤1/(X*Y) := one_div_le_one_div_of_le hz0 (by nlinarith)
  have hs : 1/X+1/Y+1/(X*Y)≤2*(1/X+1/Y) := by linarith [show 0≤1/Y by positivity]
  have ht : 1/(X*Y)+1/(X*(X*Y))+1/(Y*(X*Y))≤3/(X*Y) := by
    calc
      _ ≤ 1/(X*Y)+1/(X*Y)+1/(X*Y) := add_le_add (add_le_add_right hxx _) hyy
      _ = _ := by ring
  have hcoef : 2*L*H+H^2 ≤ (2*H+H^2)*L := by nlinarith
  have hcub : 3*L^2*H+3*L*H^2+H^3 ≤ (3*H+3*H^2+H^3)*L^2 := by
    have hll : L≤L^2 := by nlinarith
    nlinarith [mul_nonneg (show 0≤L^2-1 by nlinarith) (pow_nonneg hH.le 3),
      mul_nonneg (sub_nonneg.mpr hll) (sq_nonneg H)]
  have hb := hbound ω hω W T X Y hW hωW hT hX hY hZT
  change _ ≤ H*p^2*(1/X+1/Y+1/(X*Y)) +
    (2*L*H+H^2)*p*(1/(X*Y)+1/(X*(X*Y))+1/(Y*(X*Y))) +
    (3*L^2*H+3*L*H^2+H^3)/(X*Y*(X*Y)) at hb
  have h1 : H*p^2*(1/X+1/Y+1/(X*Y)) ≤ A*V*(L*(1/X+1/Y)) := by
    calc
      _ ≤ H*(D*V*L)*(2*(1/X+1/Y)) := by gcongr
      _ = _ := by dsimp [A]; ring
  have h2 : (2*L*H+H^2)*p*(1/(X*Y)+1/(X*(X*Y))+1/(Y*(X*Y))) ≤
      (3*(2*H+H^2)*D)*V*(L^2/(X*Y)) := by
    calc
      _ ≤ ((2*H+H^2)*L)*(D*V*L)*(3/(X*Y)) := by gcongr
      _ = _ := by ring
  have h3 : (3*L^2*H+3*L*H^2+H^3)/(X*Y*(X*Y)) ≤
      (3*H+3*H^2+H^3)*V*(L^2/(X*Y)) := by
    calc
      _ = (3*L^2*H+3*L*H^2+H^3)*(1/(X*Y*(X*Y))) := by ring
      _ ≤ ((3*H+3*H^2+H^3)*L^2)*(1/(X*Y)) := by gcongr
      _ ≤ ((3*H+3*H^2+H^3)*L^2)*(1/(X*Y))*V := le_mul_of_one_le_right (by positivity) hV
      _ = _ := by ring
  have hh : (∑ w ∈ tripleBudgetRemainderWords, ‖tripleBudgetWordError ω T X Y w‖) ≤ A*V*(L*(1/X+1/Y))+E*V*(L^2/(X*Y)) := by
    apply hb.trans
    dsimp [E]
    convert add_le_add (add_le_add h1 h2) h3 using 1 <;> ring
  apply hh.trans
  change _ ≤ (A+E)*V*(L*(1/X+1/Y)+L^2/(X*Y))
  nlinarith [mul_nonneg (show 0≤A*V by positivity) (show 0≤L^2/(X*Y) by positivity),
    mul_nonneg (show 0≤E*V by positivity) (show 0≤L*(1/X+1/Y) by positivity)]

end
end HigherCorrelations
