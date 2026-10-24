import Mathlib
import sympy.Basic
open Finset Polynomial


private lemma poly_eq_zero_of_degree_lt
  {R : Type u}
  [CommRing R]
  (n : ℕ) :
  ∀ (a : ℕ → R), (∀ i j : ℕ, i < n → j < n → i ≠ j → IsUnit (a i - a j)) →
    ∀ p : R[X], p.degree < n → (∀ i : ℕ, i < n → p.eval (a i) = 0) → p = 0 := by
  induction n with
  | zero =>
    intro a _ p hp _
    exact Polynomial.degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hp))
  | succ n ih =>
    intro a ha p hp hev
    obtain hR | hR := subsingleton_or_nontrivial R
    · exact Subsingleton.elim _ _
    have hroot : p.IsRoot (a n) := hev n (Nat.lt_succ_self n)
    have hfac : (X - C (a n)) * (p /ₘ (X - C (a n))) = p := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
    set q := p /ₘ (X - C (a n)) with hq_def
    have hq0 : q = 0 := by
      apply ih a (fun i j hi hj hij => ha i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij) q
      ·
        if hq : q = 0 then
          rw [hq, Polynomial.degree_zero]; exact WithBot.bot_lt_coe n
        else
          have hdeg : p.degree = q.degree + 1 := by
          rw [← hfac, mul_comm, Polynomial.Monic.degree_mul (Polynomial.monic_X_sub_C (a n)), Polynomial.degree_X_sub_C]
          rw [hdeg, Polynomial.degree_eq_natDegree hq] at hp
          rw [Polynomial.degree_eq_natDegree hq]
          have : q.natDegree + 1 < n + 1 := by exact_mod_cast hp
          exact_mod_cast Nat.lt_of_add_lt_add_right this
      ·
        intro i hi
        have h := hev i (Nat.lt_succ_of_lt hi)
        rw [← hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
        exact ((ha i n (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self n) (Nat.ne_of_lt hi)).mul_right_eq_zero).mp h
    rw [← hfac, hq0, mul_zero]

private lemma isUnit_pow_sub_pow
  {R : Type u}
  [CommRing R]
  {ζ : R} {m : ℕ} (hζ : ζ ^ m = 1)
  (hζu : ∀ j : ℕ, 0 < j → j < m → IsUnit (1 - ζ ^ j)) {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i ≠ j) :
  IsUnit (ζ ^ i - ζ ^ j) := by
  have hm : m ≠ 0 := by rintro rfl; exact absurd hi (Nat.not_lt_zero _)
  have hζU : IsUnit ζ := IsUnit.of_pow_eq_one hζ hm
  obtain h | h := lt_or_gt_of_ne hij
  ·
    have : ζ ^ i - ζ ^ j = ζ ^ i * (1 - ζ ^ (j - i)) := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le]
    rw [this]
    exact (hζU.pow i).mul (hζu (j - i) (Nat.sub_pos_of_lt h) (lt_of_le_of_lt (Nat.sub_le j i) hj))
  ·
    have : ζ ^ i - ζ ^ j = -(ζ ^ j * (1 - ζ ^ (i - j))) := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le, neg_sub]
    rw [this]
    exact ((hζU.pow j).mul (hζu (i - j) (Nat.sub_pos_of_lt h) (lt_of_le_of_lt (Nat.sub_le i j) hi))).neg

private lemma X_pow_sub_one_eq_prod
  {R : Type u}
  [CommRing R]
  {m : ℕ} (hm : 0 < m) {ζ : R} (hζ : ζ ^ m = 1)
  (hζu : ∀ j : ℕ, 0 < j → j < m → IsUnit (1 - ζ ^ j)) :
  (X ^ m - 1 : R[X]) = ∏ j ∈ range m, (X - C (ζ ^ j)) := by
  obtain hR | hR := subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  have hQm : (∏ j ∈ range m, (X - C (ζ ^ j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
  have hQd : (∏ j ∈ range m, (X - C (ζ ^ j))).natDegree = m := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _]
    rw [Finset.sum_congr rfl (fun j _ => Polynomial.natDegree_X_sub_C (ζ ^ j)), Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
  have hPm : (X ^ m - 1 : R[X]).Monic := by
    rw [← Polynomial.C_1]; exact Polynomial.monic_X_pow_sub_C _ hm.ne'
  have hPd : (X ^ m - 1 : R[X]).natDegree = m := by rw [← Polynomial.C_1]; apply Polynomial.natDegree_X_pow_sub_C
  rw [← sub_eq_zero]
  apply poly_eq_zero_of_degree_lt m (fun i => ζ ^ i) (fun i j hi hj hij => isUnit_pow_sub_pow hζ hζu hi hj hij)
  ·
    if h0 : (X ^ m - 1 : R[X]) - ∏ j ∈ range m, (X - C (ζ ^ j)) = 0 then
      rw [h0, Polynomial.degree_zero]; exact WithBot.bot_lt_coe m
    else
      have := Polynomial.degree_sub_lt (p := (X ^ m - 1 : R[X])) (q := ∏ j ∈ range m, (X - C (ζ ^ j)))
      (by rw [Polynomial.degree_eq_natDegree hPm.ne_zero, Polynomial.degree_eq_natDegree hQm.ne_zero, hPd, hQd])
      hPm.ne_zero (by rw [hPm.leadingCoeff, hQm.leadingCoeff])
      rwa [Polynomial.degree_eq_natDegree hPm.ne_zero, hPd] at this
  ·
    intro i hi
    rw [Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      ← pow_mul, mul_comm, pow_mul, hζ, one_pow, sub_self, Polynomial.eval_prod, zero_sub, neg_eq_zero]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

private lemma helper_main
  {R : Type u}
  [CommRing R]
  (N : ℕ) (ζ : R) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j)) :
  IsUnit ((N + 1 : ℕ) : R) := by
  classical
  obtain hR | hR := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton _
  have hfac := X_pow_sub_one_eq_prod (Nat.succ_pos N) hζ hζu
  have hD := congrArg (fun p : R[X] => (Polynomial.derivative p).eval 1) hfac
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one, sub_zero,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one, Polynomial.eval_C,
    Polynomial.derivative_prod_finset, Polynomial.eval_finset_sum, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C] at hD
  show IsUnit ((Nat.succ N : ℕ) : R)
  rw [hD, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos N))]
  ·
    rw [Polynomial.eval_prod, IsUnit.prod_iff]
    intro j hj
    obtain ⟨hj0, hjm⟩ := Finset.mem_erase.mp hj
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact hζu j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hjm)
  ·
    intro j hj hj0
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hj0, Finset.mem_range.mpr (Nat.succ_pos N)⟩)
    simp
/--
[isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {N : ℕ}
  {ζ : R}
-- given
  (hζ : ζ ^ (N + 1) = 1)
  (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j)) :
-- imply
  IsUnit ((N + 1 : ℕ) : R) :=
-- proof
  helper_main N ζ hζ hζu


-- created on 2026-10-23
