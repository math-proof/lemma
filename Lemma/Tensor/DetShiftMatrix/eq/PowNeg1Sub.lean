import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.GetShiftMatrix.eq.Ite
import sympy.matrices.dense
import sympy.matrices.expressions.permutation
open Equiv Matrix Tensor


/--
Product of `k` adjacent swaps bubbling row `j₀` down to `j₀ + k`:
`swap(j₀+k-1, j₀+k) * … * swap(j₀, j₀+1)`.
-/
private def shiftPerm (n j₀ : ℕ) (hj : j₀ < n) :
    ∀ k : ℕ, j₀ + k < n → Equiv.Perm (Fin n)
  | 0, _ => 1
  | k + 1, hk =>
    Equiv.swap ⟨j₀ + k, by omega⟩ ⟨j₀ + k + 1, hk⟩ * shiftPerm n j₀ hj k (by omega)


private lemma shiftPerm_j0 (n j₀ : ℕ) (hj : j₀ < n) (k : ℕ) (hk : j₀ + k < n) :
    shiftPerm n j₀ hj k hk ⟨j₀, hj⟩ = ⟨j₀ + k, hk⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [shiftPerm, ih]
    rfl


private lemma shiftPerm_out (n j₀ : ℕ) (hj : j₀ < n) :
    ∀ (k : ℕ) (hk : j₀ + k < n) (x : ℕ) (hx : x < n), (x < j₀ ∨ j₀ + k < x) →
      shiftPerm n j₀ hj k hk ⟨x, hx⟩ = ⟨x, hx⟩ := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _
    rfl
  | succ k ih =>
    intro hk x hx h
    rw [shiftPerm, Equiv.Perm.mul_apply]
    have h' : x < j₀ ∨ j₀ + k < x := by omega
    rw [ih (by omega) x hx h']
    apply Equiv.swap_apply_of_ne_of_ne <;> simp [Fin.ext_iff] <;> omega


private lemma shiftPerm_mid (n j₀ : ℕ) (hj : j₀ < n) (t k : ℕ) (ht1 : 1 ≤ t)
    (htk : t ≤ k) (hk : j₀ + k < n) :
    shiftPerm n j₀ hj k hk ⟨j₀ + t, by omega⟩ = ⟨j₀ + t - 1, by omega⟩ := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases ht : t ≤ k
    · rw [shiftPerm, Equiv.Perm.mul_apply, ih ht (by omega)]
      apply Equiv.swap_apply_of_ne_of_ne <;> simp [Fin.ext_iff] <;> omega
    · have htk' : t = k + 1 := by omega
      subst htk'
      rw [shiftPerm, Equiv.Perm.mul_apply]
      have hfix : shiftPerm n j₀ hj k (by omega) ⟨j₀ + (k + 1), by omega⟩ = ⟨j₀ + (k + 1), by omega⟩ :=
        shiftPerm_out n j₀ hj k (by omega) (j₀ + (k + 1)) (by omega) (by omega)
      rw [hfix]
      have harg : (⟨j₀ + (k + 1), by omega⟩ : Fin n) = ⟨j₀ + k + 1, by omega⟩ := rfl
      rw [harg, Equiv.swap_apply_right]
      apply Fin.ext
      rfl


/--
Determinant of the elementary row-shift matrix:
`det(ShiftMatrix(n, i₀, j₀)) = (-1)^(i₀ - j₀)` when `j₀ < i₀`
(moving row `i₀` to position `j₀` takes `i₀ - j₀` adjacent swaps).
-/
@[main]
private lemma main
  [CommRing α] [CharZero α]
  (n i₀ j₀ : ℕ)
  (hi₀ : i₀ < n)
  (h : j₀ < i₀) :
-- imply
  (ShiftMatrix (α := α) n i₀ j₀).det = (-1) ^ (i₀ - j₀) := by
-- proof
  have hj : j₀ < n := by omega
  let k := i₀ - j₀
  have hk : j₀ + k < n := by omega
  let σ : Equiv.Perm (Fin n) := shiftPerm n j₀ hj k hk
  have hσ1 : σ ⟨j₀, hj⟩ = ⟨i₀, hi₀⟩ := by
    have h := shiftPerm_j0 n j₀ hj k hk
    have hki : j₀ + k = i₀ := by
      show j₀ + (i₀ - j₀) = i₀
      omega
    exact Fin.ext (congrArg (fun x : Fin n => (x : ℕ)) h |>.trans hki)
  have hσ2 : ∀ (x : Fin n), j₀ < (x : ℕ) → (x : ℕ) ≤ i₀ → σ x = ⟨(x : ℕ) - 1, by omega⟩ := by
    intro x hx1 hx2
    have htk1 : 1 ≤ (x : ℕ) - j₀ := by omega
    have htk : (x : ℕ) - j₀ ≤ k := by omega
    have hxb : j₀ + ((x : ℕ) - j₀) < n := by omega
    have heq0 : j₀ + ((x : ℕ) - j₀) = (x : ℕ) := by omega
    have heq : x = ⟨j₀ + ((x : ℕ) - j₀), hxb⟩ := by
      apply Fin.ext
      exact heq0.symm
    rw [heq]
    exact_mod_cast shiftPerm_mid n j₀ hj ((x : ℕ) - j₀) k htk1 htk hk
  have hσ3 : ∀ (x : Fin n), ((x : ℕ) < j₀ ∨ i₀ < (x : ℕ)) → σ x = x := by
    intro x hlt
    exact_mod_cast shiftPerm_out n j₀ hj k hk (x : ℕ) x.isLt (by omega)
  have hT : (ShiftMatrix (α := α) n i₀ j₀).toMatrix = (1 : Matrix (Fin n) (Fin n) (Tensor α [])).submatrix σ id := by
    ext i j
    have hentry := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ i j
    simp only [GetElem.getElem, Nat.Delta.eq.Ite] at hentry
    simp only [Tensor.toMatrix, Matrix.submatrix, Matrix.one_apply, Matrix.of_apply, id, GetElem.getElem]
    rw [hentry]
    simp only [← Fin.val_eq_val]
    if hi : (i : ℕ) = j₀ then
      · have hsi : σ i = ⟨i₀, hi₀⟩ := by
          have hi' : i = ⟨j₀, hj⟩ := Fin.ext hi
          rw [hi']
          exact hσ1
        simp only [hsi]
        split_ifs <;> first | rfl | (exfalso; omega) | erw [Nat.cast_one] | erw [Nat.cast_zero]
    else if hmid : j₀ < (i : ℕ) ∧ (i : ℕ) ≤ i₀ then
      · simp only [hσ2 i hmid.1 hmid.2]
        split_ifs <;> first | rfl | (exfalso; omega) | erw [Nat.cast_one] | erw [Nat.cast_zero]
    else
      · simp only [hσ3 i (by omega)]
        split_ifs <;> first | rfl | (exfalso; omega) | erw [Nat.cast_one] | erw [Nat.cast_zero]
  have hsign : ∀ m : ℕ, ∀ (hm : j₀ + m < n), Equiv.Perm.sign (shiftPerm n j₀ hj m hm) = (-1 : Units ℤ) ^ m := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [shiftPerm, Equiv.Perm.sign_one]
    | succ m ih =>
      intro hmk1
      have hmk : j₀ + m < n := by omega
      let a : Fin n := ⟨j₀ + m, hmk⟩
      let b : Fin n := ⟨j₀ + m + 1, hmk1⟩
      have hval : (j₀ + m : ℕ) ≠ j₀ + m + 1 := by omega
      have hne : a ≠ b := fun hcon => hval (congrArg Fin.val hcon)
      have hstep : shiftPerm n j₀ hj (m + 1) hmk1 = Equiv.swap a b * shiftPerm n j₀ hj m hmk := by
        rfl
      rw [hstep, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, ih hmk]
      rw [pow_succ']
  apply Eq.trans (Det.eq.DetToMatrix (ShiftMatrix (α := α) n i₀ j₀))
  rw [hT, Matrix.det_permute, Matrix.det_one, mul_one]
  rw [hsign k hk]
  simp
  norm_cast


-- created on 2026-09-10
