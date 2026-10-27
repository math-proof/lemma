import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma valuation_lt_iff_div_mem_nonunits [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) (x y : L) (hy : y ≠ 0) : A.valuation x < A.valuation y ↔ x / y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_div₀, div_lt_one₀]
  apply (zero_lt_iff.mpr ((map_ne_zero A.valuation).mpr hy))

private noncomputable def IsWildAt [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) (σ : L ≃ₐ[K] L) : Prop := ∀ z : L, z ≠ 0 → A.valuation (σ z - z) < A.valuation z

private lemma isWildAt_of_forall_mem_nonunits [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (h : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits) : IsWildAt A σ := by
  intro z hz
  rw [valuation_lt_iff_div_mem_nonunits A (σ z - z) z hz, sub_div, div_self hz, div_eq_mul_inv]
  apply h z hz

private lemma IsWildAt.valuation_apply [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (hw : IsWildAt A σ) (w : L) : A.valuation (σ w) = A.valuation w := by
  if hw0 : w = 0 then
    subst hw0
    simp
  else
    have h := Valuation.map_add_eq_of_lt_right A.valuation (hw w hw0)
    rwa [sub_add_cancel] at h

private lemma IsWildAt.pow [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (hw : IsWildAt A σ) (n : ℕ) : IsWildAt A (σ ^ n) := by
  induction n
  ·
    intro z hz
    simp [(map_ne_zero A.valuation).mpr hz, zero_lt_iff]
  ·
    rename_i n ih
    intro z hz
    have hsplit : (σ ^ (n + 1)) z - z = σ ((σ ^ n) z - z) + (σ z - z) := by
      rw [pow_succ', AlgEquiv.mul_apply, map_sub]
      ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ (hw z hz)
    rw [IsWildAt.valuation_apply A hw]
    apply ih z hz

private lemma valuation_natCast_eq_one_of_coprime [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {q m : ℕ} (hq : A.valuation (q : L) < 1) (hm : Nat.Coprime m q) : A.valuation (m : L) = 1 := by
  have hle : A.valuation (m : L) ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff]
    apply natCast_mem A m
  by_contra hne
  have hlt : A.valuation (m : L) < 1 := lt_of_le_of_ne hle hne
  have hg : (Int.gcd m q : ℤ) = 1 := by
    exact_mod_cast hm
  have hb := Int.gcd_eq_gcd_ab m q
  rw [hg] at hb
  have h1 : (1 : L) = (m : L) * (Int.gcdA m q : L) + (q : L) * (Int.gcdB m q : L) := by
    exact_mod_cast congrArg (Int.cast : ℤ → L) hb
  have : A.valuation (1 : L) < 1 := by
    rw [h1]
    refine Valuation.map_add_lt _ ?_ ?_
    ·
      rw [map_mul]
      apply mul_lt_one_of_lt_of_le hlt
      rw [ValuationSubring.valuation_le_one_iff]
      apply intCast_mem A
    ·
      rw [map_mul]
      apply mul_lt_one_of_lt_of_le hq
      rw [ValuationSubring.valuation_le_one_iff]
      apply intCast_mem A
  rw [map_one] at this
  apply lt_irrefl _ this

private lemma IsWildAt.apply_eq_of_pow_apply_eq [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (hw : IsWildAt A σ) {q m : ℕ} (hq : A.valuation (q : L) < 1) (hm : Nat.Coprime m q) (y : L) (hy : (σ ^ m) y = y) : σ y = y := by
  by_contra hne
  set w := σ y - y with hwdef
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  have htel : (Finset.range m).sum (fun i => (σ ^ i) w) = 0 := by
    have h := Finset.sum_range_sub (fun i => (σ ^ i) y) m
    rw [pow_zero, AlgEquiv.one_apply] at h
    rw [hy, sub_self] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, map_sub, ← AlgEquiv.mul_apply, ← pow_succ]
  have hdec : (Finset.range m).sum (fun i => (σ ^ i) w) = (m : L) * w + (Finset.range m).sum (fun i => (σ ^ i) w - w) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hS : A.valuation ((Finset.range m).sum (fun i => (σ ^ i) w - w)) < A.valuation ((m : L) * w) := by
    rw [map_mul, valuation_natCast_eq_one_of_coprime A hq hm, one_mul]
    apply Valuation.map_sum_lt A.valuation ((map_ne_zero A.valuation).mpr hw0) (fun i _ => (IsWildAt.pow A hw i) w hw0)
  have hval : A.valuation ((Finset.range m).sum (fun i => (σ ^ i) w)) = A.valuation ((m : L) * w) := by
    rw [hdec, add_comm]
    apply Valuation.map_add_eq_of_lt_right A.valuation hS
  rw [htel, map_zero, map_mul, valuation_natCast_eq_one_of_coprime A hq hm, one_mul, eq_comm, map_eq_zero] at hval
  apply hw0 hval

/--
[ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild.lean)
-/
@[path]
private lemma main
  [Field K] [Field L] [Algebra K L]
  (A : ValuationSubring L)
  {q : ℕ} (hA : ((q : ℕ) : L) ∈ A.nonunits)
  {σ : L ≃ₐ[K] L}
  (hwild : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits)
  {m : ℕ} (hm : m.Coprime q)
  {y : L} (h : (σ ^ m) y = y) :
  -- imply
  σ y = y :=
  IsWildAt.apply_eq_of_pow_apply_eq A (isWildAt_of_forall_mem_nonunits A hwild) ((ValuationSubring.mem_nonunits_iff A).mp hA) hm y h


-- created on 2026-10-20
