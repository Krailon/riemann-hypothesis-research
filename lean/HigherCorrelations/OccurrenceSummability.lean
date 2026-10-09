import HigherCorrelations.SummabilityDefinitions
import HigherCorrelations.FinitePatterns

/-! UNCONDITIONAL implications from explicit shell counts and decay bounds.
No zero-count estimate is assumed as an axiom or imported from quasi-RH.
-/
namespace HigherCorrelations
open Filter
open scoped Topology

theorem dyadic_ratio_bounds (d p : ℕ) (hp : d < p) :
    0 ≤ dyadicRatio d p ∧ dyadicRatio d p < 1 := by
  unfold dyadicRatio
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).mpr
    exact pow_lt_pow_right₀ (by norm_num) hp

theorem shell_sum_eq {I : Type*} (S : OccurrenceShells I) (f : I → ℝ) (n : ℕ) :
    (∑' i : {i // S.shell i = n}, f i) = ∑ i ∈ S.members n, f i := by
  have h : {i | S.shell i = n} = (S.members n : Set I) := by
    ext i; exact (S.mem_iff i n).symm
  change (∑' i : {i | S.shell i = n}, f i) = _
  rw [h]
  exact (S.members n).tsum_subtype f

theorem summable_of_shell_bounds {I : Type*} (S : OccurrenceShells I)
    (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) (B : ℕ → ℝ) (hB : Summable B)
    (hbound : ∀ n, (∑ i ∈ S.members n, f i) ≤ B n) : Summable f := by
  have hpart : ∀ i, ∃! n, i ∈ {i | S.shell i = n} := by
    intro i; exact ⟨S.shell i, rfl, fun n hn => hn.symm⟩
  apply (summable_partition hf hpart).mpr
  constructor
  · intro n
    have h : {i | S.shell i = n} = (S.members n : Set I) := by
      ext i; exact (S.mem_iff i n).symm
    rw [h]
    exact (hasSum_fintype _).summable
  · apply hB.of_norm_bounded
    intro n
    change ‖∑' i : {i // S.shell i = n}, f i‖ ≤ B n
    rw [shell_sum_eq, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => hf i)]
    exact hbound n

theorem dyadic_shell_sum_bound {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (_hC : 0 ≤ C) (d p : ℕ)
    (hcount : ∀ n, ((S.members n).card : ℝ) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (hdecay : ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i) (n : ℕ) :
    (∑ i ∈ S.members n, ‖f i‖) ≤ A * C * dyadicRatio d p ^ n := by
  calc
    _ ≤ ∑ _i ∈ S.members n, A / ((2 : ℝ) ^ p) ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [(S.mem_iff i n).mp hi] using hdecay i
    _ = ((S.members n).card : ℝ) * (A / ((2 : ℝ) ^ p) ^ n) := by simp
    _ ≤ (C * ((2 : ℝ) ^ d) ^ n) * (A / ((2 : ℝ) ^ p) ^ n) :=
      mul_le_mul_of_nonneg_right (hcount n) (by positivity)
    _ = _ := by rw [dyadicRatio, div_pow]; ring

theorem dyadic_summable_norm {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (d p : ℕ) (hp : d < p)
    (hcount : ∀ n, ((S.members n).card : ℝ) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (hdecay : ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i) :
    Summable (fun i => ‖f i‖) := by
  have hr := dyadic_ratio_bounds d p hp
  exact summable_of_shell_bounds S _ (fun i => norm_nonneg _) _
    ((summable_geometric_of_lt_one hr.1 hr.2).mul_left (A * C))
    (dyadic_shell_sum_bound S f A C hA hC d p hcount hdecay)

theorem dyadic_summable {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (d p : ℕ) (hp : d < p)
    (hcount : ∀ n, ((S.members n).card : ℝ) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (hdecay : ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i) : Summable f :=
  (dyadic_summable_norm S f A C hA hC d p hp hcount hdecay).of_norm

theorem radius_decay_to_shell {I : Type*} (S : OccurrenceShells I)
    (f : I → ℂ) (r : I → ℝ) (A : ℝ) (hA : 0 ≤ A) (p : ℕ)
    (hr : ∀ i, (2 : ℝ) ^ S.shell i ≤ 1 + r i)
    (hf : ∀ i, ‖f i‖ ≤ A / (1 + r i) ^ p) :
    ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i := by
  intro i
  apply (hf i).trans
  have hpow : ((2 : ℝ) ^ S.shell i) ^ p ≤ (1 + r i) ^ p :=
    pow_le_pow_left₀ (by positivity) (hr i) p
  rw [← pow_mul, Nat.mul_comm, pow_mul] at hpow
  exact div_le_div_of_nonneg_left hA (by positivity) hpow

theorem shell_tsum_eq {I : Type*} (S : OccurrenceShells I) (f : I → ℝ)
    (hf : Summable f) :
    (∑' i, f i) = ∑' n, ∑ i ∈ S.members n, f i := by
  have h := (hf.hasSum.tsum_fiberwise S.shell).tsum_eq.symm
  change (∑' i, f i) = ∑' n, ∑' i : {i // S.shell i = n}, f i at h
  simpa only [shell_sum_eq] using h

theorem geometric_tail_eq (a : ℕ → ℝ) (N : ℕ) :
    (∑' n, if N ≤ n then a n else 0) = ∑' n, a (n + N) := by
  let e : ℕ ≃ {n : ℕ // N ≤ n} :=
    { toFun := fun n => ⟨n + N, by omega⟩
      invFun := fun n => n.val - N
      left_inv := by intro n; simp
      right_inv := by intro n; ext; dsimp; omega }
  have h := tsum_subtype {n | N ≤ n} a
  simp only [Set.indicator_apply, Set.mem_ofPred_eq] at h
  rw [← h]
  exact (e.tsum_eq (fun n => a n.val)).symm

theorem dyadic_tail_bound {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (d p : ℕ) (hp : d < p)
    (hcount : ∀ n, ((S.members n).card : ℝ) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (hdecay : ∀ i, ‖f i‖ ≤ A / ((2 : ℝ) ^ p) ^ S.shell i) (N : ℕ) :
    (∑' i : {i // N ≤ S.shell i}, ‖f i‖) ≤
      A * C * dyadicRatio d p ^ N / (1 - dyadicRatio d p) := by
  classical
  have hf := dyadic_summable_norm S f A C hA hC d p hp hcount hdecay
  have hr := dyadic_ratio_bounds d p hp
  have hgeom := summable_geometric_of_lt_one hr.1 hr.2
  have htail : Summable (fun i => if N ≤ S.shell i then ‖f i‖ else 0) :=
    by
      apply (hf.indicator {i | N ≤ S.shell i}).congr
      intro i
      simp [Set.indicator_apply]
  have heq : (∑' i : {i // N ≤ S.shell i}, ‖f i‖) =
      ∑' n, ∑ i ∈ S.members (n + N), ‖f i‖ := by
    have h := tsum_subtype {i | N ≤ S.shell i} (fun i => ‖f i‖)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq] at h
    have hh : (∑' i : {i // N ≤ S.shell i}, ‖f i‖) =
        ∑' i, if N ≤ S.shell i then ‖f i‖ else 0 := h
    rw [hh, shell_tsum_eq S _ htail]
    have hinner (n : ℕ) :
        (∑ i ∈ S.members n, if N ≤ S.shell i then ‖f i‖ else 0) =
          if N ≤ n then ∑ i ∈ S.members n, ‖f i‖ else 0 := by
      trans ∑ i ∈ S.members n, if N ≤ n then ‖f i‖ else 0
      · apply Finset.sum_congr rfl
        intro i hi
        rw [(S.mem_iff i n).mp hi]
      · split_ifs <;> simp
    simp_rw [hinner]
    exact geometric_tail_eq _ N
  rw [heq]
  have hs : Summable (fun n => ∑ i ∈ S.members (n + N), ‖f i‖) := by
    have hg := (hf.hasSum.tsum_fiberwise S.shell).summable
    have hh : Summable (fun n => ∑ i ∈ S.members n, ‖f i‖) := by
      change Summable (fun n => ∑' i : {i // S.shell i = n}, ‖f i‖) at hg
      exact hg.congr (shell_sum_eq S (fun i => ‖f i‖))
    exact hh.comp_injective (fun a b h => Nat.add_right_cancel h)
  calc
    _ ≤ ∑' n, (A * C * dyadicRatio d p ^ N) * dyadicRatio d p ^ n := by
      apply hs.tsum_le_tsum _ (hgeom.mul_left _)
      intro n
      have h := dyadic_shell_sum_bound S f A C hA hC d p hcount hdecay (n + N)
      rw [pow_add] at h
      convert h using 1; ring
    _ = _ := by
      rw [hgeom.tsum_mul_left, tsum_geometric_of_lt_one hr.1 hr.2]
      rfl

theorem project_dyadic_ratios :
    dyadicRatio 4 20 = (1 / 65536 : ℝ) ∧
    dyadicRatio 4 22 = (1 / 262144 : ℝ) := by
  norm_num [dyadicRatio]

end HigherCorrelations
