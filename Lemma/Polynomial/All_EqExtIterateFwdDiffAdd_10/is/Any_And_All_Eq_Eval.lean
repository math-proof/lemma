import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial Finset


/-- ported from external source -/

noncomputable def binom
  {R : Type*}
  [Field R]
  (k : ℕ) : R[X] := C ((k.factorial : R)⁻¹) * descPochhammer R k

noncomputable def newton
  {R : Type*}
  [Field R]
  (f : ℤ → R) (d : ℕ) (y : ℤ) : R[X] :=
  ∑ k ∈ range (d + 1), C ((fwdDiff (1 : ℤ))^[k] f y) * (binom k).comp (X - C (y : R))

private lemma  binom_eval_natCast
  {R : Type*}
  [Field R]
  [CharZero R] (k n : ℕ) :
  (binom k : R[X]).eval (n : R) = (n.choose k : R) := by
  unfold binom
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial R n k,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul]

private lemma  natDegree_binom_le
  {R : Type*}
  [Field R]
  (k : ℕ) : (binom k : R[X]).natDegree ≤ k := by
  unfold binom
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [descPochhammer_natDegree]

private lemma  natDegree_newton_le
  {R : Type*}
  [Field R]
  (f : ℤ → R) (d : ℕ) (y : ℤ) : (newton f d y).natDegree ≤ d := by
  unfold newton
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_comp_le.trans ?_
  rw [natDegree_X_sub_C, mul_one]
  exact (natDegree_binom_le k).trans (Nat.lt_succ_iff.mp (mem_range.mp hk))

private lemma  newton_eval
  {R : Type*}
  [Field R]
  [CharZero R] (f : ℤ → R) (d : ℕ) (y : ℤ) (n : ℕ) :
  (newton f d y).eval ((y + n : ℤ) : R) =
    ∑ k ∈ range (d + 1), (n.choose k : R) * (fwdDiff (1 : ℤ))^[k] f y := by
  unfold newton
  rw [eval_finsetSum]
  refine sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C, Int.cast_add, Int.cast_natCast,
    add_sub_cancel_left, binom_eval_natCast, mul_comm]

private lemma  iter_zero
  {R : Type*}
  [Field R]
  (i : ℕ) : (fwdDiff (1 : ℤ))^[i] (0 : ℤ → R) = 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    have : fwdDiff (1 : ℤ) (0 : ℤ → R) = 0 := by
      funext n
      simp [fwdDiff]
    rw [this, ih]

private lemma  iter_eq_zero_of_le
  {R : Type*}
  [Field R]
  {f : ℤ → R} {d : ℕ} (h : ∀ n, (fwdDiff (1 : ℤ))^[d + 1] f n = 0)
  {j : ℕ} (hj : d + 1 ≤ j) (n : ℤ) : (fwdDiff (1 : ℤ))^[j] f n = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [add_comm, Function.iterate_add_apply]
  have hz : (fwdDiff (1 : ℤ))^[d + 1] f = 0 := funext h
  rw [hz, iter_zero]
  rfl

private lemma  eq_newton_eval
  {R : Type*}
  [Field R]
  [CharZero R] {f : ℤ → R} {d : ℕ}
  (h : ∀ n, (fwdDiff (1 : ℤ))^[d + 1] f n = 0) (y : ℤ) (n : ℕ) :
  f (y + n) = (newton f d y).eval ((y + n : ℤ) : R) := by
  have hsub1 : range (n + 1) ⊆ range (n + 1 + d) := range_subset_range.mpr (Nat.le_add_right _ _)
  have hsub2 : range (d + 1) ⊆ range (n + 1 + d) := range_subset_range.mpr (by omega)
  have hL : f (y + n) = ∑ k ∈ range (n + 1 + d), (n.choose k : R) * (fwdDiff (1 : ℤ))^[k] f y := by
    have key := shift_eq_sum_fwdDiff_iter (1 : ℤ) f n y
    rw [nsmul_eq_mul, mul_one] at key
    rw [key]
    simp_rw [nsmul_eq_mul]
    refine sum_subset hsub1 fun k _ hk => ?_
    have hnk : n < k := by
      rw [mem_range] at hk
      omega
    rw [Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero, zero_mul]
  have hR : (newton f d y).eval ((y + n : ℤ) : R) =
      ∑ k ∈ range (n + 1 + d), (n.choose k : R) * (fwdDiff (1 : ℤ))^[k] f y := by
    rw [newton_eval]
    refine sum_subset hsub2 fun k _ hk => ?_
    have hdk : d + 1 ≤ k := by
      rw [mem_range] at hk
      omega
    rw [iter_eq_zero_of_le h hdk, mul_zero]
  rw [hL, hR]

private lemma  newton_eq_newton
  {R : Type*}
  [Field R]
  [CharZero R] {f : ℤ → R} {d : ℕ}
  (h : ∀ n, (fwdDiff (1 : ℤ))^[d + 1] f n = 0) (y y' : ℤ) :
  newton f d y = newton f d y' := by
  wlog hle : y ≤ y' generalizing y y'
  · exact (this y' y (le_of_not_ge hle)).symm
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((y' + n : ℤ) : R)) ?_ ?_
  ·
    intro a b hab
    have hab' : (y' + a : ℤ) = y' + b := Int.cast_injective hab
    exact_mod_cast add_left_cancel hab'
  ·
    intro n
    have hm : (y' + n : ℤ) = y + (((y' - y).toNat + n : ℕ) : ℤ) := by
      rw [Nat.cast_add, Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
      ring
    show (newton f d y).eval ((y' + n : ℤ) : R) = (newton f d y').eval ((y' + n : ℤ) : R)
    rw [← eq_newton_eval h y' n, hm, ← eq_newton_eval h y]

private lemma  exists_polynomial
  {R : Type*}
  [Field R]
  [CharZero R] {f : ℤ → R} {d : ℕ}
  (h : ∀ n, (fwdDiff (1 : ℤ))^[d + 1] f n = 0) :
  ∃ p : R[X], p.natDegree ≤ d ∧ ∀ n : ℤ, f n = p.eval (n : R) := by
  refine ⟨newton f d 0, natDegree_newton_le f d 0, fun n => ?_⟩
  have h1 := eq_newton_eval h n 0
  simp only [Nat.cast_zero, add_zero] at h1
  rwa [newton_eq_newton h 0 n]

private lemma  iter_eq_zero_of_polynomial
  {R : Type*}
  [Field R]
  {f : ℤ → R} {d : ℕ} (p : R[X]) (hp : p.natDegree ≤ d)
  (hf : ∀ n : ℤ, f n = p.eval (n : R)) (n : ℤ) :
  (fwdDiff (1 : ℤ))^[d + 1] f n = 0 := by
  have hP : (fwdDiff (1 : R))^[d + 1] (fun x : R => p.eval x) (n : R) = 0 := by
    rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (Nat.lt_succ_of_le hp)]
    rfl
  rw [fwdDiff_iter_eq_sum_shift] at hP ⊢
  rw [← hP]
  refine sum_congr rfl fun k _ => ?_
  rw [hf]
  congr 1
  simp only [nsmul_eq_mul, mul_one, Int.cast_add, Int.cast_natCast]

private lemma helper_main
  {R : Type*}
  [Field R]
  [CharZero R] (f : ℤ → R) (d : ℕ) :
  (∀ n : ℤ, (fwdDiff (1 : ℤ))^[d + 1] f n = 0) ↔
    ∃ p : Polynomial R, p.natDegree ≤ d ∧ ∀ n : ℤ, f n = p.eval (n : R) :=
  ⟨exists_polynomial, fun ⟨p, hp, hf⟩ n => iter_eq_zero_of_polynomial p hp hf n⟩
@[path]
private lemma main
  [Field R] [CharZero R]
  {f : ℤ → R}
  {d : ℕ} :
-- imply
  (∀ n : ℤ, (fwdDiff (1 : ℤ))^[d + 1] f n = 0) ↔
      ∃ p : Polynomial R, p.natDegree ≤ d ∧ ∀ n : ℤ, f n = p.eval (n : R) :=
-- proof
  helper_main f d


-- created on 2026-10-23
