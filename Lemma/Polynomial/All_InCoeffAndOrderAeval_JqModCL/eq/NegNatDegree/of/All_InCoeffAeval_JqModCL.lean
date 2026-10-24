import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_JqCoeff
import Lemma.Int.P2MUtil

open Polynomial ModularCurve

/--
[ModularCurve_forall_coeff_mem_of_forall_coeff_aeval_jqModC_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_forall_coeff_mem_of_forall_coeff_aeval_jqModC_mem.lean)
-/

private lemma  algebraMap_laurent
  {L : Type*}
  [Field L]
  (c : L) : algebraMap L (LaurentSeries L) c = HahnSeries.C c := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  show HahnSeries.ofPowerSeries ℤ L (algebraMap L (PowerSeries L) c) = _
  rw [← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]

private lemma  coeff_algebraMap_mul
  {L : Type*}
  [Field L]
  (c : L) (x : LaurentSeries L) (m : ℤ) :
  (algebraMap L (LaurentSeries L) c * x).coeff m = c * x.coeff m := by
  rw [algebraMap_laurent, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

private lemma  jqModC_pow
  {L : Type*}
  [Field L]
  (n : ℕ) :
  jqModC L ^ n = HahnSeries.single (-(n : ℤ)) 1 *
    HahnSeries.ofPowerSeries ℤ L ((jNum ^ n).map (Int.castRingHom L)) := by
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, ← map_pow, ← map_pow]
  congr 2
  simp

private lemma  coeff_jqModC_pow
  {L : Type*}
  [Field L]
  (n : ℕ) (m : ℤ) :
  (jqModC L ^ n).coeff m =
    if m + n < 0 then 0 else (((jNum ^ n).coeff (m + n).toNat : ℤ) : L) := by
  rw [jqModC_pow]
  have hm : m = (m + n) + (-(n : ℤ)) := by ring
  conv_lhs => rw [hm]
  rw [HahnSeries.coeff_single_mul_add, one_mul]
  split_ifs with hlt
  · exact ofPowerSeries_coeff_of_neg _ hlt
  ·
    have h0 : 0 ≤ m + n := by omega
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hk, Int.toNat_natCast]
    rw [show ((k : ℕ) : ℤ) = (k : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      eq_intCast]

private lemma  coeff_jqModC_pow_of_lt
  {L : Type*}
  [Field L]
  {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : (jqModC L ^ n).coeff m = 0 := by
  rw [coeff_jqModC_pow, ite_eq_left (by omega)]

private lemma  coeff_jqModC_pow_self
  {L : Type*}
  [Field L]
  (n : ℕ) : (jqModC L ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [coeff_jqModC_pow, ite_eq_right (by omega)]
  have : (-(n : ℤ) + n).toNat = 0 := by simp
  rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_jNum, one_pow, Int.cast_one]

private lemma  coeff_jqModC_pow_mem
  {L : Type*}
  [Field L]
  (R : Subring L) (n : ℕ) (m : ℤ) : (jqModC L ^ n).coeff m ∈ R := by
  rw [coeff_jqModC_pow]
  split_ifs
  · exact R.zero_mem
  · exact intCast_mem R _

private lemma  coeff_finset_sum
  {L : Type*}
  [Field L]
  {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries L) (m : ℤ) :
  (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HahnSeries.coeff_add, ih]

private lemma  coeff_aeval
  {L : Type*}
  [Field L]
  (P : Polynomial L) (m : ℤ) :
  (aeval (jqModC L) P).coeff m = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (jqModC L ^ i).coeff m := by
  conv_lhs => rw [aeval_eq_sum_range]
  rw [coeff_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, coeff_algebraMap_mul]

private lemma  coeff_aeval_neg_natDegree
  {L : Type*}
  [Field L]
  (P : Polynomial L) :
  (aeval (jqModC L) P).coeff (-(P.natDegree : ℤ)) = P.leadingCoeff := by
  rw [coeff_aeval, Finset.sum_eq_single_of_mem P.natDegree (Finset.mem_range.mpr (Nat.lt_succ_self _))]
  ·
    rw [coeff_jqModC_pow_self, mul_one]
    rfl
  ·
    intro i hi hne
    have hi' : i < P.natDegree := by rw [Finset.mem_range] at hi; omega
    rw [coeff_jqModC_pow_of_lt (by omega), mul_zero]

private lemma  coeff_aeval_of_lt
  {L : Type*}
  [Field L]
  (P : Polynomial L) {m : ℤ} (hm : m < -(P.natDegree : ℤ)) :
  (aeval (jqModC L) P).coeff m = 0 := by
  rw [coeff_aeval]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [coeff_jqModC_pow_of_lt (by omega), mul_zero]

private lemma  coeff_mem
  {L : Type*}
  [Field L]
  (R : Subring L) : ∀ (N : ℕ) (P : Polynomial L), P.natDegree ≤ N →
  (∀ n : ℤ, (aeval (jqModC L) P).coeff n ∈ R) → ∀ i : ℕ, P.coeff i ∈ R := by
  intro N
  induction N with
  | zero =>
    intro P hP h i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    ·
      have h0 := h 0
      have hlead := coeff_aeval_neg_natDegree (L := L) P
      rw [Nat.le_zero.mp hP] at hlead
      simp only [Nat.cast_zero, neg_zero] at hlead
      rw [hlead] at h0
      rwa [Polynomial.leadingCoeff, Nat.le_zero.mp hP] at h0
    ·
      rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      apply R.zero_mem
  | succ N ih =>
    intro P hP h i
    have htop : P.coeff (N + 1) ∈ R := by
      by_cases hdeg : P.natDegree = N + 1
      ·
        have h1 := h (-((N + 1 : ℕ) : ℤ))
        rw [← hdeg, coeff_aeval_neg_natDegree] at h1
        rw [← hdeg]; exact h1
      ·
        rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        apply R.zero_mem
    set c := P.coeff (N + 1) with hc
    set P' := P - C c * X ^ (N + 1) with hP'
    have hP'coeff : ∀ i, P'.coeff i = if i = N + 1 then 0 else P.coeff i := by
      intro i
      rw [hP', coeff_sub, coeff_C_mul_X_pow]
      split_ifs with hi
      · rw [hi, hc, sub_self]
      · rw [sub_zero]
    have hP'deg : P'.natDegree ≤ N := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      rw [hP'coeff]
      split_ifs with hi'
      · rfl
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    have hP'aeval : ∀ n : ℤ, (aeval (jqModC L) P').coeff n ∈ R := by
      intro n
      have : aeval (jqModC L) P' = aeval (jqModC L) P - algebraMap L (LaurentSeries L) c * jqModC L ^ (N + 1) := by
        rw [hP', map_sub, map_mul, aeval_C, map_pow, aeval_X]
      rw [this, HahnSeries.coeff_sub, coeff_algebraMap_mul]
      exact R.sub_mem (h n) (R.mul_mem htop (coeff_jqModC_pow_mem R _ _))
    have hIH := ih P' hP'deg hP'aeval
    by_cases hi : i = N + 1
    ·
      rwa [hi]
    ·
      have := hIH i
      rwa [hP'coeff, ite_eq_right hi] at this
@[path]
private lemma main
  [Field L]
  {R : Subring L}
  {P : Polynomial L}
-- given
  (h : ∀ n : ℤ, (Polynomial.aeval (ModularCurve.jqModC L) P).coeff n ∈ R) :
-- imply
  (∀ i : ℕ, P.coeff i ∈ R) ∧
      (P ≠ 0 → (Polynomial.aeval (ModularCurve.jqModC L) P).order = -(P.natDegree : ℤ)) := by
  classical
  refine ⟨coeff_mem R P.natDegree P le_rfl h, fun hP => ?_⟩
  have hlead : (aeval (jqModC L) P).coeff (-(P.natDegree : ℤ)) ≠ 0 := by
-- proof
    rw [coeff_aeval_neg_natDegree]; exact leadingCoeff_ne_zero.mpr hP
  have hne : aeval (jqModC L) P ≠ 0 := fun h0 => hlead (by rw [h0]; rfl)
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero hlead
  ·
    by_contra hlt
    push Not at hlt
    exact hne (HahnSeries.coeff_order_eq_zero.mp (coeff_aeval_of_lt P hlt))


-- created on 2026-10-23
