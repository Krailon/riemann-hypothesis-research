import HigherCorrelations.TriplePrimeResonanceDefinitions
import HigherCorrelations.TriplePrimeFourier

/-! UNCONDITIONAL exact prime-power resonance classification and reindexing.
All parameters are fixed before any infinite series is regrouped. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

private theorem xy_ge_one (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) : 1≤X*Y := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]

theorem pairMeanPrimeCoefficient_ne_zero (X : ℝ) (hX : 1≤X) (n : ℕ) :
    pairMeanPrimeCoefficient X n ≠ 0 ↔ IsPrimePow (n+1) := by
  have hXp : 0<X := by linarith
  have hm : 0 < min ((n+1:ℝ)/X) (X/(n+1:ℝ)) := by positivity
  unfold pairMeanPrimeCoefficient
  constructor
  · intro h
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1)
  · intro h
    exact mul_ne_zero (mul_ne_zero (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr h)
      (Real.exp_pos _).ne') hm.ne'

theorem triplePrimeCoefficient_ne_zero (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y)
    (v : PrimeTriple) : triplePrimeCoefficient X Y v ≠ 0 ↔ ∀ r, IsPrimePow (v r+1) := by
  simp only [triplePrimeCoefficient,mul_ne_zero_iff,
    pairMeanPrimeCoefficient_ne_zero X hX,pairMeanPrimeCoefficient_ne_zero Y hY,
    pairMeanPrimeCoefficient_ne_zero (X*Y) (xy_ge_one X Y hX hY)]
  constructor
  · rintro ⟨⟨h0,h1⟩,h2⟩ r
    fin_cases r <;> assumption
  · intro h
    exact ⟨⟨h 0,h 1⟩,h 2⟩

/-- Equality of positive powers determines both the prime and the exponent. -/
theorem primePower_unique (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime)
    (ha : 0<a) (hb : 0<b) (he : p^a=q^b) : p=q ∧ a=b := by
  have hd : p ∣ q^b := he ▸ dvd_pow_self p (by omega : a≠0)
  have hpq := Nat.prime_eq_prime_of_dvd_pow hp hq hd
  subst q
  exact ⟨rfl, Nat.pow_right_injective hp.two_le he⟩

theorem primePowerIndex_values (q : PrimePowerParameters) :
    (primePowerIndex q 0+1 = q.1.val^q.2.1.val) ∧
    (primePowerIndex q 1+1 = q.1.val^q.2.2.val) ∧
    (primePowerIndex q 2+1 = q.1.val^(q.2.1.val+q.2.2.val)) := by
  have hp : 0<q.1.val := q.1.property.pos
  exact ⟨Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne')),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne')),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne'))⟩

theorem primePowerIndex_injective : Function.Injective primePowerIndex := by
  intro q s he
  have h0 : q.1.val^q.2.1.val = s.1.val^s.2.1.val := by
    rw [← (primePowerIndex_values q).1,← (primePowerIndex_values s).1,he]
  have h1 : q.1.val^q.2.2.val = s.1.val^s.2.2.val := by
    rw [← (primePowerIndex_values q).2.1,← (primePowerIndex_values s).2.1,he]
  have ha := primePower_unique _ _ _ _ q.1.property s.1.property q.2.1.property s.2.1.property h0
  have hb := primePower_unique _ _ _ _ q.1.property s.1.property q.2.2.property s.2.2.property h1
  exact Prod.ext (Subtype.ext ha.1) (Prod.ext (Subtype.ext ha.2) (Subtype.ext hb.2))

theorem primePowerIndex_supported (q : PrimePowerParameters) :
    triplePrimeResonant (primePowerIndex q) ∧ ∀ r, IsPrimePow (primePowerIndex q r+1) := by
  have h := primePowerIndex_values q
  constructor
  · change (primePowerIndex q 0+1)*(primePowerIndex q 1+1) = primePowerIndex q 2+1
    rw [h.1,h.2.1,h.2.2,pow_add]
  · intro r
    fin_cases r
    · change IsPrimePow (primePowerIndex q 0+1)
      rw [h.1]; exact q.1.property.isPrimePow.pow q.2.1.property.ne'
    · change IsPrimePow (primePowerIndex q 1+1)
      rw [h.2.1]; exact q.1.property.isPrimePow.pow q.2.2.property.ne'
    · change IsPrimePow (primePowerIndex q 2+1)
      rw [h.2.2]; exact q.1.property.isPrimePow.pow (Nat.ne_of_gt (Nat.add_pos_left q.2.1.property _))

/-- Positive prime powers whose product is a prime power have the same prime. -/
theorem primePower_resonance_exists (m n k : ℕ) (hm : IsPrimePow m)
    (hn : IsPrimePow n) (hk : IsPrimePow k) (he : m*n=k) :
    ∃ q : PrimePowerParameters, m=q.1.val^q.2.1.val ∧ n=q.1.val^q.2.2.val ∧
      k=q.1.val^(q.2.1.val+q.2.2.val) := by
  obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff m).mp hm
  obtain ⟨s,b,hs,hb,rfl⟩ := (isPrimePow_nat_iff n).mp hn
  obtain ⟨r,c,hr,hc,rfl⟩ := (isPrimePow_nat_iff k).mp hk
  have hpr : p=r := Nat.prime_eq_prime_of_dvd_pow hp hr
    (he ▸ dvd_mul_of_dvd_left (dvd_pow_self p (by omega : a≠0)) _)
  have hsr : s=r := Nat.prime_eq_prime_of_dvd_pow hs hr
    (he ▸ dvd_mul_of_dvd_right (dvd_pow_self s (by omega : b≠0)) _)
  subst p
  subst s
  refine ⟨⟨⟨r,hr⟩,⟨a,ha⟩,⟨b,hb⟩⟩,rfl,rfl,?_⟩
  simpa only [pow_add] using he.symm

theorem triplePrimeResonance_classification (v : PrimeTriple) :
    (triplePrimeResonant v ∧ ∀ r, IsPrimePow (v r+1)) ↔
      ∃! q : PrimePowerParameters, primePowerIndex q = v := by
  constructor
  · rintro ⟨hv,hp⟩
    obtain ⟨q,h0,h1,h2⟩ := primePower_resonance_exists _ _ _ (hp 0) (hp 1) (hp 2) hv
    have he : primePowerIndex q=v := by
      funext r
      have h := primePowerIndex_values q
      fin_cases r
      · change primePowerIndex q 0 = v 0
        omega
      · change primePowerIndex q 1 = v 1
        omega
      · change primePowerIndex q 2 = v 2
        omega
    exact ⟨q,he,fun s hs => primePowerIndex_injective (hs.trans he.symm)⟩
  · rintro ⟨q,rfl,_⟩
    exact primePowerIndex_supported q

/-- Arithmetic support, not nonvanishing of a weight-dependent Fourier term. -/
theorem triplePrimeResonance_nonzero (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (v : PrimeTriple) :
    (triplePrimeResonant v ∧ triplePrimeCoefficient X Y v ≠ 0) ↔
      ∃! q : PrimePowerParameters, primePowerIndex q=v := by
  rw [triplePrimeCoefficient_ne_zero X Y hX hY,triplePrimeResonance_classification]

/-- A genuine bijection with the arithmetic support of the resonant series. -/
theorem primePowerIndex_bijective : ∃ e : PrimePowerParameters ≃ SupportedPrimeResonance,
    ∀ q, (e q).val = primePowerIndex q := by
  let f : PrimePowerParameters → SupportedPrimeResonance :=
    fun q => ⟨primePowerIndex q,primePowerIndex_supported q⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q s he
      exact primePowerIndex_injective (congrArg Subtype.val he)
    · intro v
      obtain ⟨q,hq,_⟩ := (triplePrimeResonance_classification v.val).mp v.property
      exact ⟨q,Subtype.ext hq⟩
  exact ⟨Equiv.ofBijective f hf,fun _ => rfl⟩

theorem primePower_resonance_unique (m n k : ℕ) :
    (m*n=k ∧ ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n *
      ArithmeticFunction.vonMangoldt k ≠ 0) ↔
    ∃! q : PrimePowerParameters, m=q.1.val^q.2.1.val ∧ n=q.1.val^q.2.2.val ∧
      k=q.1.val^(q.2.1.val+q.2.2.val) := by
  simp only [mul_ne_zero_iff,ArithmeticFunction.vonMangoldt_ne_zero_iff]
  constructor
  · rintro ⟨he,⟨⟨hm,hn⟩,hk⟩⟩
    obtain ⟨q,hq⟩ := primePower_resonance_exists m n k hm hn hk he
    refine ⟨q,hq,?_⟩
    intro s hs
    have ha := primePower_unique _ _ _ _ s.1.property q.1.property
      s.2.1.property q.2.1.property (hs.1.symm.trans hq.1)
    have hb := primePower_unique _ _ _ _ s.1.property q.1.property
      s.2.2.property q.2.2.property (hs.2.1.symm.trans hq.2.1)
    exact Prod.ext (Subtype.ext ha.1) (Prod.ext (Subtype.ext ha.2) (Subtype.ext hb.2))
  · rintro ⟨q,⟨rfl,rfl,rfl⟩,_⟩
    exact ⟨(pow_add _ _ _).symm,
      ⟨⟨q.1.property.isPrimePow.pow q.2.1.property.ne',
        q.1.property.isPrimePow.pow q.2.2.property.ne'⟩,
        q.1.property.isPrimePow.pow (Nat.ne_of_gt (Nat.add_pos_left q.2.1.property _))⟩⟩

private def resonantIndex (q : PrimePowerParameters) : {v : PrimeTriple // triplePrimeResonant v} :=
  ⟨primePowerIndex q,(primePowerIndex_supported q).1⟩

private theorem resonantIndex_injective : Function.Injective resonantIndex := by
  intro q s h
  exact primePowerIndex_injective (congrArg Subtype.val h)

theorem triplePrimeResonantMass_summable (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun q : PrimePowerParameters => triplePrimeCoefficient X Y (primePowerIndex q)) :=
  (triplePrimeCoefficient_summable X Y hX hY).comp_injective primePowerIndex_injective

theorem triplePrimeResonantMass_norm_summable (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun q : PrimePowerParameters => ‖triplePrimeCoefficient X Y (primePowerIndex q)‖) := by
  simpa only [Real.norm_eq_abs,abs_of_nonneg (triplePrimeCoefficient_nonneg X Y hX hY _)] using
    triplePrimeResonantMass_summable X Y hX hY

/-- Reindex only the nonzero coefficients, retaining zero terms in the ambient subtype. -/
theorem triplePrimeResonantMass_reindex (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    (∑' v : {v : PrimeTriple // triplePrimeResonant v}, triplePrimeCoefficient X Y v.val) =
      triplePrimeResonantMass X Y := by
  unfold triplePrimeResonantMass
  symm
  apply resonantIndex_injective.tsum_eq (f := fun v : {v : PrimeTriple // triplePrimeResonant v} => triplePrimeCoefficient X Y v.val)
  intro v hv
  have hc : triplePrimeCoefficient X Y v.val ≠ 0 := hv
  obtain ⟨q,hq,_⟩ := (triplePrimeResonance_nonzero X Y hX hY v.val).mp ⟨v.property,hc⟩
  exact ⟨q,Subtype.ext hq⟩

theorem triplePrimeResonantMass_nested (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    triplePrimeResonantMass X Y =
      ∑' p : {p : ℕ // p.Prime}, ∑' a : {a : ℕ // 0<a}, ∑' b : {b : ℕ // 0<b},
        triplePrimeCoefficient X Y (primePowerIndex (p,a,b)) := by
  have h := triplePrimeResonantMass_summable X Y hX hY
  change (∑' q : PrimePowerParameters, triplePrimeCoefficient X Y (primePowerIndex q)) = _
  rw [h.tsum_prod]
  apply tsum_congr
  intro p
  exact (h.prod_factor p).tsum_prod

theorem triplePrimeResonantMass_nonneg (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    0 ≤ triplePrimeResonantMass X Y :=
  tsum_nonneg (fun q => triplePrimeCoefficient_nonneg X Y hX hY _)

theorem triplePrimeResonantMass_bound (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    triplePrimeResonantMass X Y ≤ triplePrimeMass X*triplePrimeMass Y*triplePrimeMass (X*Y) := by
  rw [← triplePrimeResonantMass_reindex X Y hX hY,← triplePrimeCoefficient_mass X Y hX hY]
  exact Summable.tsum_subtype_le _ _ (triplePrimeCoefficient_nonneg X Y hX hY)
    (triplePrimeCoefficient_summable X Y hX hY)

theorem triplePrime_resonant_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : {v : PrimeTriple // triplePrimeResonant v} =>
      ‖triplePrimeFourierTerm ω T X Y v.val‖) :=
  (triplePrimeFourier_summable ω hω hs T X Y hT hX hY).comp_injective Subtype.val_injective

theorem triplePrime_off_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : {v : PrimeTriple // ¬triplePrimeResonant v} =>
      ‖triplePrimeFourierTerm ω T X Y v.val‖) :=
  (triplePrimeFourier_summable ω hω hs T X Y hT hX hY).comp_injective Subtype.val_injective

/-- The smoothing mass is retained; it is not assumed to be one. -/
theorem triplePrime_resonant_series (ω : ℝ → ℝ) (T X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    (∑' v : {v : PrimeTriple // triplePrimeResonant v}, triplePrimeFourierTerm ω T X Y v.val) =
      (∫ u : ℝ, (ω u:ℂ))*(triplePrimeResonantMass X Y:ℂ) := by
  calc
    _ = ∑' v : {v : PrimeTriple // triplePrimeResonant v},
        (triplePrimeCoefficient X Y v.val:ℂ)*(∫ u : ℝ, (ω u:ℂ)) := by
      apply tsum_congr
      intro v
      exact triplePrimeFourier_resonance ω T X Y v.val v.property
    _ = _ := by
      rw [tsum_mul_right,← Complex.ofReal_tsum, triplePrimeResonantMass_reindex X Y hX hY,mul_comm]

theorem triplePrime_resonance_split (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleWordIntegral ω T X Y ![.P,.P,.P] =
      (∫ u : ℝ, (ω u:ℂ))*(triplePrimeResonantMass X Y:ℂ)+triplePrimeOffSeries ω T X Y := by
  rw [triplePrime_fourier_identity ω hω hs T X Y hT hX hY]
  have he := Summable.tsum_add_tsum_compl
    (s := {v : PrimeTriple | triplePrimeResonant v})
    (f := triplePrimeFourierTerm ω T X Y)
    (triplePrime_resonant_norm_summable ω hω hs T X Y hT hX hY).of_norm
    (triplePrime_off_norm_summable ω hω hs T X Y hT hX hY).of_norm
  rw [← he]
  change (∑' v : {v : PrimeTriple // triplePrimeResonant v}, triplePrimeFourierTerm ω T X Y v.val) +
    triplePrimeOffSeries ω T X Y = _
  rw [triplePrime_resonant_series ω T X Y hX hY]

theorem triplePrime_resonance_signed (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    (tripleWordSign ![.P,.P,.P]:ℂ)*tripleWordIntegral ω T X Y ![.P,.P,.P] =
      -(∫ u : ℝ, (ω u:ℂ))*(triplePrimeResonantMass X Y:ℂ)-triplePrimeOffSeries ω T X Y := by
  rw [triplePrime_resonance_split ω hω hs T X Y hT hX hY]
  have hsign : tripleWordSign ![.P,.P,.P] = -1 := by decide
  rw [hsign]
  push_cast
  ring

theorem triplePrime_resonance_unit_mass (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (hm : ∫ u : ℝ, (ω u:ℂ) = 1) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleWordIntegral ω T X Y ![.P,.P,.P] =
      (triplePrimeResonantMass X Y:ℂ)+triplePrimeOffSeries ω T X Y := by
  rw [triplePrime_resonance_split ω hω hs T X Y hT hX hY,hm,one_mul]

/-- No prime-power coefficient is supported at the integer one. -/
theorem primePowerIndex_excludes_one (q : PrimePowerParameters) (r : Fin 3) :
    primePowerIndex q r ≠ 0 := by
  have h := (primePowerIndex_supported q).2 r
  intro hz
  exact h.ne_one (by simp [hz])

theorem primePowerIndex_equal_exponents (p : {p : ℕ // p.Prime}) (a : {a : ℕ // 0<a}) :
    primePowerIndex (p,a,a) 0 = primePowerIndex (p,a,a) 1 := rfl

/-- Unequal exponents remain ordered; they are not identified by a permutation. -/
theorem primePowerIndex_ordered (p : {p : ℕ // p.Prime}) (a b : {a : ℕ // 0<a}) (hab : a≠b) :
    primePowerIndex (p,a,b) ≠ primePowerIndex (p,b,a) := by
  intro h
  have he := primePowerIndex_injective h
  exact hab (congrArg (fun q : PrimePowerParameters => q.2.1) he)

theorem primePowerIndex_first :
    primePowerIndex (⟨2,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩) = ![1,1,3] := by
  decide

theorem primePower_distinct_product (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    ¬IsPrimePow (p*q) := by
  intro h
  obtain ⟨r,hm,hn,_⟩ := primePower_resonance_exists p q (p*q) hp.isPrimePow hq.isPrimePow h rfl
  have ha := primePower_unique p r.1.val 1 r.2.1.val hp r.1.property (by omega)
    r.2.1.property (by simpa using hm)
  have hb := primePower_unique q r.1.val 1 r.2.2.val hq r.1.property (by omega)
    r.2.2.property (by simpa using hn)
  exact hne (ha.1.trans hb.1.symm)

theorem triplePrimeResonance_two_three (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    triplePrimeResonant ![1,2,5] ∧ triplePrimeCoefficient X Y ![1,2,5] = 0 := by
  refine ⟨by norm_num [triplePrimeResonant], ?_⟩
  by_contra h
  have hp := (triplePrimeCoefficient_ne_zero X Y hX hY _).mp h 2
  exact primePower_distinct_product 2 3 (by decide) (by decide) (by decide) hp

theorem triplePrimeOffSeries_zero_weight (T X Y : ℝ) :
    triplePrimeOffSeries (fun _ => 0) T X Y = 0 := by
  simp [triplePrimeOffSeries,triplePrimeFourier_zero_weight]

theorem triplePrimeOffSeries_neg_weight (ω : ℝ → ℝ) (T X Y : ℝ) :
    triplePrimeOffSeries (fun t => -ω t) T X Y = -triplePrimeOffSeries ω T X Y := by
  simp only [triplePrimeOffSeries,triplePrimeFourier_neg_weight,tsum_neg]

theorem triplePrime_resonance_minimal (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) :
    tripleWordIntegral ω 3 1 1 ![.P,.P,.P] =
      (∫ u : ℝ, (ω u:ℂ))*(triplePrimeResonantMass 1 1:ℂ)+triplePrimeOffSeries ω 3 1 1 :=
  triplePrime_resonance_split ω hω hs 3 1 1 (by norm_num) (by norm_num) (by norm_num)

end
end HigherCorrelations
