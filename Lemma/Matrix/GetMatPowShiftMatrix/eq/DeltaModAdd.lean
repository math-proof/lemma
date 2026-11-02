import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Defs
import Lemma.Matrix.GetShiftMatrix.eq.DeltaModAdd_1
import Lemma.Nat.Delta.eq.Ite
open Matrix Nat


private lemma add_one_mod_eq
  {n a : ℕ} :
    ((a % n) + 1) % n = (a + 1) % n :=
  Nat.mod_add_mod a n 1

@[path]
private lemma main
  [Semiring α]
-- given
  (k : ℕ)
  (i j : Fin n) :
-- imply
  (shiftMatrix (α := α) ⟨0, i.pos⟩ ⟨n - 1, by have := i.pos; omega⟩ ^ k) i j =
    (KroneckerDelta (((i : ℕ) + k) % n) (j : ℕ) : α) := by
-- proof
  let M := shiftMatrix (α := α) ⟨0, i.pos⟩ ⟨n - 1, by have := i.pos; omega⟩
  induction k generalizing i j with
  | zero =>
    change (1 : Matrix (Fin n) (Fin n) α) i j =
      (KroneckerDelta (((i : ℕ) + 0) % n) (j : ℕ) : α)
    have hi : ((i : ℕ) + 0) % n = (i : ℕ) := by
      simp [Nat.mod_eq_of_lt i.isLt]
    rw [hi, Delta.eq.Ite]
    if h : i = j then
      rw [h, Matrix.one_apply_eq]
      simp
    else
      have hval : (i : ℕ) ≠ (j : ℕ) := fun e => h (Fin.ext e)
      simp [Matrix.one_apply_ne h, hval]
  | succ k ih =>
    change (M ^ (k + 1)) i j = _
    rw [pow_succ, Matrix.mul_apply]
    have hterm (t : Fin n) :
      (M ^ k) i t * M t j =
        (KroneckerDelta (((i : ℕ) + k) % n) (t : ℕ) : α) *
          KroneckerDelta (((t : ℕ) + 1) % n) (j : ℕ) := by
      rw [ih i t]
      have hM :
        M t j = (KroneckerDelta (((t : ℕ) + 1) % n) (j : ℕ) : α) := by
        simpa [M] using GetShiftMatrix.eq.DeltaModAdd_1 (α := α) n t j
      rw [hM]
    simp_rw [hterm]
    let t0 : Fin n := ⟨((i : ℕ) + k) % n, Nat.mod_lt _ i.pos⟩
    have ht0 : (t0 : ℕ) = ((i : ℕ) + k) % n := rfl
    rw [Finset.sum_eq_single t0]
    ·
      have hδ1 :
        KroneckerDelta (((i : ℕ) + k) % n) (t0 : ℕ) = (1 : α) := by
        rw [Delta.eq.Ite, ite_eq_left ht0.symm, Nat.cast_one]
      simp only [hδ1, one_mul]
      have hmod : ((t0 : ℕ) + 1) % n = ((i : ℕ) + (k + 1)) % n := calc
        _ = (((i : ℕ) + k) % n + 1) % n := by rw [ht0]
        _ = (((i : ℕ) + k) + 1) % n := add_one_mod_eq
        _ = ((i : ℕ) + (k + 1)) % n := by rw [Nat.add_assoc]
      rw [hmod]
    ·
      intro t _ ht
      have hne : (t : ℕ) ≠ ((i : ℕ) + k) % n := by
        intro e
        exact ht (Fin.ext (e.trans ht0.symm))
      have hδ0 :
        KroneckerDelta (((i : ℕ) + k) % n) (t : ℕ) = (0 : α) := by
        rw [Delta.eq.Ite, ite_eq_right (Ne.symm hne), Nat.cast_zero]
      simp [hδ0]
    ·
      intro h
      exact (h (Finset.mem_univ t0)).elim


-- created on 2026-11-01
