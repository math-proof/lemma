import Mathlib
import Lemma.TateCurve.XMultStructure
import Def.TateCurve_XMultIdentities

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section EngineWiring

theorem eq_zero_of_master_rows {B : ℝ} {c : ℕ → ℕ → K} {q u g : K}
    (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha c w M + specTail c w M + specGamma c M)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M) g) :
    g = 0 := by
  have hzero := spec_eq_zero_of_master hB hc hmaster
  have hfun : (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M) = fun _ => 0 := by
    funext M
    have hsum0 : ∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k + u⁻¹ ^ k - 2) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' := Finset.mem_Icc.mp hk
      rw [hzero M k hk'.1 hk'.2, zero_mul]
    rw [hsum0, zero_mul]
  rw [hfun] at hrepr
  exact hrepr.unique hasSum_zero

end EngineWiring

section UnitSpectatorFamily

variable {q : K}


lemma nnnorm_unitSpectator (_hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    ‖unitSpectator q n‖₊ = 1 := by
  have hpow : ‖q ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero n)
  have hpowlt : ‖q ^ (n + 1)‖₊ < 1 := by exact_mod_cast hpow
  have hne : ‖(1 : K)‖₊ ≠ ‖q ^ (n + 1)‖₊ := by
    rw [nnnorm_one]
    exact ne_of_gt hpowlt
  unfold unitSpectator
  rw [nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hne, nnnorm_one]
  exact max_eq_left (le_of_lt hpowlt)

lemma norm_unitSpectator (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    ‖unitSpectator q n‖ = 1 := by
  have h := nnnorm_unitSpectator hq0 hq n
  rw [← coe_nnnorm, h, NNReal.coe_one]

lemma unitSpectator_ne_zero (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    unitSpectator q n ≠ 0 := by
  intro h
  have h1 := norm_unitSpectator hq0 hq n
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

lemma unitSpectator_ne_one (hq0 : q ≠ 0) (n : ℕ) : unitSpectator q n ≠ 1 := by
  unfold unitSpectator
  intro h
  have h1 : q ^ (n + 1) = 0 := by
    have h2 := congrArg (fun z => z - 1) h
    simpa using h2
  exact pow_ne_zero (n + 1) hq0 h1

lemma offLattice_unitSpectator (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    OffLattice q (unitSpectator q n) :=
  offLattice_of_norm_eq_one hq0 hq (norm_unitSpectator hq0 hq n) (unitSpectator_ne_one hq0 n)

lemma addParams_unitSpectator (hq0 : q ≠ 0) {u : K} (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1)
    (n : ℕ) : AddParams q u (unitSpectator q n) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  exact addParams_of_norm_one_spectator hq0 hu hqu (norm_unitSpectator hq0 hq1 n)
    (unitSpectator_ne_one hq0 n)

private lemma pow_succ_ne_of_lt (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {a b : ℕ} (hab : a < b) :
    q ^ (a + 1) ≠ q ^ (b + 1) := by
  intro h
  have hfac : q ^ (b + 1) = q ^ (a + 1) * q ^ (b - a) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hfac] at h
  have hqa : q ^ (a + 1) ≠ 0 := pow_ne_zero _ hq0
  nth_rewrite 1 [← mul_one (q ^ (a + 1))] at h
  have h1 : (1 : K) = q ^ (b - a) := mul_left_cancel₀ hqa h
  have h2 : ‖q ^ (b - a)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  rw [← h1, norm_one] at h2
  exact lt_irrefl _ h2

lemma unitSpectator_injective (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    Function.Injective (unitSpectator q) := by
  intro a b hab
  unfold unitSpectator at hab
  have hpow : q ^ (a + 1) = q ^ (b + 1) := by
    have h := congrArg (fun z => z - 1) hab
    simpa using h
  by_contra hne
  rcases Nat.lt_or_ge a b with h | h
  · exact pow_succ_ne_of_lt hq0 hq h hpow
  · have hba : b < a := by omega
    exact pow_succ_ne_of_lt hq0 hq hba hpow.symm

end UnitSpectatorFamily

section LaurentVanishing

lemma laurent_eval_eq_zero_of_infinite_roots {s : Finset ℤ} {a : ℤ → K} {S : Set K}
    (hS : S.Infinite) (hS0 : ∀ v ∈ S, v ≠ 0)
    (hvan : ∀ v ∈ S, ∑ j ∈ s, a j * v ^ j = 0) :
    ∀ v : K, v ≠ 0 → ∑ j ∈ s, a j * v ^ j = 0 := by
  classical

  set D : ℕ := s.sup fun j => (-j).toNat with hD
  have hDle : ∀ j ∈ s, (0 : ℤ) ≤ j + (D : ℤ) := by
    intro j hj
    have h1 : (-j).toNat ≤ D := Finset.le_sup (f := fun j => (-j).toNat) hj
    omega

  set p : Polynomial K := ∑ j ∈ s, Polynomial.C (a j) * Polynomial.X ^ (j + (D : ℤ)).toNat
    with hp

  have heval : ∀ v : K, v ≠ 0 → p.eval v = (∑ j ∈ s, a j * v ^ j) * v ^ D := by
    intro v hv
    rw [hp, Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have h0 : (0 : ℤ) ≤ j + (D : ℤ) := hDle j hj
    have h1 : v ^ ((j + (D : ℤ)).toNat) = v ^ (j + (D : ℤ)) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg h0]
    rw [h1, zpow_add₀ hv, zpow_natCast]
    ring

  have hp0 : p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot p (hS.mono ?_)
    intro v hvS
    have h1 := heval v (hS0 v hvS)
    have h2 : p.eval v = 0 := by
      rw [h1, hvan v hvS, zero_mul]
    exact h2

  intro v hv
  have h1 := heval v hv
  rw [hp0, Polynomial.eval_zero] at h1
  have hvD : v ^ D ≠ 0 := pow_ne_zero _ hv
  rcases mul_eq_zero.mp h1.symm with h | h
  · exact h
  · exact absurd h hvD

end LaurentVanishing

section SpectatorUpgrade

variable {q : K}


lemma norm_spectatorRows_le {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K} {B : ℝ}
    (hB : 0 ≤ B) (ha : ∀ M k j, ‖a M k j‖ ≤ B) {v : K} (hv : ‖v‖ = 1) (M k : ℕ) :
    ‖spectatorRows s a v M k‖ ≤ B :=
  norm_finsetSum_mul_zpow_le_of_norm_eq_one hv hB (fun j _ => ha M k j)

theorem rows_eval_eq_zero_of_master_at_spectators
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {B : ℝ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M) :
    ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 → ∑ j ∈ s M k, a M k j * v ^ j = 0 := by
  intro M k hk1 hkM

  have hvan : ∀ n : ℕ, ∑ j ∈ s M k, a M k j * (unitSpectator q n) ^ j = 0 := by
    intro n
    have hbound : ∀ N k', ‖spectatorRows s a (unitSpectator q n) N k'‖ ≤ B :=
      fun N k' => norm_spectatorRows_le hB ha (norm_unitSpectator hq0 hq n) N k'
    exact spec_eq_zero_of_master hB hbound (hmaster n) M k hk1 hkM

  refine laurent_eval_eq_zero_of_infinite_roots
    (Set.infinite_range_of_injective (unitSpectator_injective hq0 hq)) ?_ ?_
  · rintro v ⟨n, rfl⟩
    exact unitSpectator_ne_zero hq0 hq n
  · rintro v ⟨n, rfl⟩
    exact hvan n

end SpectatorUpgrade

section ConditionalConclusions

variable {q u v : K}

theorem symAdd_sum_of_rows {B : ℝ} {c : ℕ → ℕ → K}
    (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha c w M + specTail c w M + specGamma c M)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M) (addDefectSum q u v)) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) :=
  addDefectSum_eq_zero_iff.mp (eq_zero_of_master_rows hB hc hmaster hrepr)

theorem symAdd_prod_of_rows {B : ℝ} {c : ℕ → ℕ → K}
    (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha c w M + specTail c w M + specGamma c M)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M) (addDefectProd q u v)) :
    pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
      symProdNum q (pointX q u) (pointX q v) :=
  addDefectProd_eq_zero_iff.mp (eq_zero_of_master_rows hB hc hmaster hrepr)

private lemma laurentRows_repr_eq_zero {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (hzero : ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 →
      ∑ j ∈ s M k, a M k j * v ^ j = 0)
    (hv0 : v ≠ 0) :
    (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M)
      = fun _ => 0 := by
  funext M
  have hsum0 : ∑ k ∈ Finset.Icc 1 M,
      (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k + u⁻¹ ^ k - 2) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    rw [hzero M k hk'.1 hk'.2 v hv0, zero_mul]
  rw [hsum0, zero_mul]

theorem symAdd_sum_of_laurentRows (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {B : ℝ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K} (ha : ∀ M k j, ‖a M k j‖ ≤ B)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M)
    (hv0 : v ≠ 0)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M)
      (addDefectSum q u v)) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) := by
  have hzero := rows_eval_eq_zero_of_master_at_spectators hq0 hq hB ha hmaster
  rw [laurentRows_repr_eq_zero hzero hv0] at hrepr
  exact addDefectSum_eq_zero_iff.mp (hrepr.unique hasSum_zero)

theorem symAdd_prod_of_laurentRows (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {B : ℝ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K} (ha : ∀ M k j, ‖a M k j‖ ≤ B)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M)
    (hv0 : v ≠ 0)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M)
      (addDefectProd q u v)) :
    pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
      symProdNum q (pointX q u) (pointX q v) := by
  have hzero := rows_eval_eq_zero_of_master_at_spectators hq0 hq hB ha hmaster
  rw [laurentRows_repr_eq_zero hzero hv0] at hrepr
  exact addDefectProd_eq_zero_iff.mp (hrepr.unique hasSum_zero)

end ConditionalConclusions

end TateCurve
