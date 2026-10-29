import HigherCorrelations.TripleBoundaryIntegrated

/-! UNCONDITIONAL absolute, uniform integrated boundary budget. Constants are
existential through the checked arithmetic estimates; no effectiveness claim
or height asymptotic is silently added. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

set_option maxHeartbeats 800000 in
private theorem normalize_budget (A H D R K W V T b L P : ℝ)
    (hA : 0≤A) (hH : 0≤H) (hD : 0≤D) (hR : 0≤R) (hK : 0≤K)
    (hW : 0≤W) (hV : 0≤V) (hT : 3≤T) (hb : 1≤b) (hL : 0≤L)
    (hLK : L≤K*b) (hcube : L^3/T≤81) (hP : 0≤P) :
    A*(1+V)*(L^2/(4*b^2)+L^3/T+P)+H*(1+W)*(2*L/b+L^2/b^2)+
      (2*D*L/b+8/T+55296*R/b^2) ≤
    (A*(K^2+82)+H*(2*K+K^2)+2*D*K+8+55296*R)*(1+W+V)*(1+P) := by
  let S := 1+W+V
  let C := A*(K^2+82)+H*(2*K+K^2)+2*D*K+8+55296*R
  have hs : 1≤S := by dsimp [S]; linarith
  have hb0 : 0<b := by linarith
  have hT0 : 0<T := by linarith
  have hr : L/b≤K := (div_le_iff₀ hb0).mpr hLK
  have hr2 : L^2/b^2≤K^2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_nonneg hL hb0.le) hr 2
  have hr4 : L^2/(4*b^2)≤K^2 := by
    apply le_trans _ hr2
    apply div_le_div_of_nonneg_left (sq_nonneg L) (sq_pos_of_pos hb0)
    nlinarith [sq_nonneg b]
  have h12 : 2*L/b+L^2/b^2≤2*K+K^2 := by
    have htwo := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ)≤2)
    have hh := add_le_add htwo hr2
    convert hh using 1 <;> ring
  have h3 : 2*D*L/b+8/T+55296*R/b^2≤2*D*K+8+55296*R := by
    have hd := mul_le_mul_of_nonneg_left hr (show 0≤2*D by positivity)
    have ht' : (8:ℝ)/T≤8 := div_le_self (by norm_num) (by linarith)
    have hb2 : 1≤b^2 := by nlinarith
    have hres : 55296*R/b^2≤55296*R := div_le_self (by positivity) hb2
    convert add_le_add (add_le_add hd ht') hres using 1 <;> ring
  have h1 : A*(1+V)*(L^2/(4*b^2)+L^3/T+P)≤S*(A*(K^2+81+P)) := by
    have hvS : 1+V≤S := by dsimp [S]; linarith
    have hx := add_le_add_right (add_le_add hr4 hcube) P
    have hp' : L^2/(4*b^2)+L^3/T+P≤K^2+81+P := by linarith only [hx]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hvS hA) hp'
      (by positivity : 0≤L^2/(4*b^2)+L^3/T+P) (by positivity : 0≤A*S)
    convert hh using 1 <;> ring
  have h2 : H*(1+W)*(2*L/b+L^2/b^2)≤S*(H*(2*K+K^2)) := by
    have hwS : 1+W≤S := by dsimp [S]; linarith
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hwS hH) h12
      (by positivity : 0≤2*L/b+L^2/b^2) (by positivity : 0≤H*S)
    convert hh using 1 <;> ring
  have h3' : 2*D*L/b+8/T+55296*R/b^2≤S*(2*D*K+8+55296*R) :=
    h3.trans (le_mul_of_one_le_left (by positivity) hs)
  apply (add_le_add (add_le_add h1 h2) h3').trans
  have hCA : 0≤C-A := by
    dsimp [C]
    nlinarith only [mul_nonneg hA (sq_nonneg K),hA,
      mul_nonneg hH (show 0≤2*K+K^2 by positivity),
      mul_nonneg (show 0≤2*D by positivity) hK,hR]
  have hpC := mul_nonneg hCA hP
  have hlast : A*(K^2+81+P)+H*(2*K+K^2)+(2*D*K+8+55296*R)≤C*(1+P) := by
    dsimp [C] at hpC ⊢
    nlinarith only [hpC,hA]
  have hh := mul_le_mul_of_nonneg_left hlast (show 0≤S by linarith)
  convert hh using 1 <;> dsimp [C,S] <;> ring

set_option maxHeartbeats 800000 in
theorem tripleBoundary_uniform_integrated : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T κ M : ℝ,
    0≤W → (∀ u, ω u≤W) → 2*Real.pi*Real.exp 1≤T → 0<κ → 0≤M →
    ∀ (ψ : ℝ × ℝ → ℂ), (∀ p ∈ tripleQuadrant, ‖ψ p‖≤M) →
    (∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ) →
    (∫ p : ℝ × ℝ, ‖tripleQuadrantAmplitude ψ p*
      tripleQuadrantRemainder ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)‖) ≤
    C*M*(1+W+fourierDerivativeL1 ω 1)*(1+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^4) := by
  obtain ⟨A,hA,H,hH,D,hD,h⟩ := tripleBoundary_integrated_envelope
  let K := tripleBoundaryLogConstant
  let R := tripleResonanceDecayConstant
  have hK : 0<K := tripleBoundaryLogConstant_pos
  have hR : 0<R := tripleResonanceDecayConstant_pos
  let C := A*(K^2+82)+H*(2*K+K^2)+2*D*K+8+55296*R
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ω hω W T κ M hW hωW hT hκ hM ψ hψ hs
  obtain ⟨ht,hb,hq,hL⟩ := tripleBoundary_height T hT
  have ht3 := (tripleTestBase_bounds T ht).1
  have htB : 0<tripleTestBase T := by linarith [(tripleTestBase_bounds T ht).2.1]
  have hh := h ω hω W T κ M hW hωW ht hκ hM ψ hψ hs
  apply hh.trans
  have hbnd := normalize_budget A H D R K W (fourierDerivativeL1 ω 1) T
    (Real.log (tripleTestBase T)) (Real.log (2*T+2))
    ((tripleTestBase T)^(-κ)*Real.log (2*T+2)^4) hA.le hH.le hD.le hR.le hK.le hW
    (fourierDerivativeL1_nonneg ω 1) ht3 hb
    (le_trans (by norm_num) (tripleBudget_height_log T ht3)) hL
    (tripleBoundary_height_cube T ht3) (by positivity)
  convert mul_le_mul_of_nonneg_left hbnd hM using 1 <;> dsimp [C,R,K] <;> ring

end
end HigherCorrelations
