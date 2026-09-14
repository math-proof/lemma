import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Pow.eq.TensorListPow
import sympy.matrices.dense
import torch.stack
open Matrix Tensor


/--
`det (J - 1) = (-1)^(n-1) * (n - 1)` where `J` is the all-ones matrix,
by the matrix determinant lemma with `J` a column times a row of ones.
-/
private lemma det_ite (γ : Type*) [CommRing γ] (n : ℕ) (h : 0 < n) :
    Matrix.det (fun i j : Fin n => if i = j then (0 : γ) else 1) =
      (-1 : γ) ^ (n - 1) * (n - 1 : ℕ) := by
  let u : Fin n → γ := fun _ => 1
  let J := Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) u
  have hJ : ∀ (i j : Fin n), J i j = (1 : γ) := by
    intro i j
    simp only [J, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · simp only [u]
      exact one_mul (1 : γ)
    · intro x _ hx
      exact False.elim (hx (Fin.fin_one_eq_zero x))
    · intro hx
      exact False.elim (hx (Finset.mem_univ (0 : Fin 1)))
  have hM : (fun i j : Fin n => if i = j then (0 : γ) else 1) =
      J - (1 : Matrix (Fin n) (Fin n) γ) := by
    ext i j
    rw [Matrix.sub_apply, hJ i j, Matrix.one_apply]
    split_ifs <;> simp
  rw [hM]
  have hneg : J - (1 : Matrix (Fin n) (Fin n) γ) =
      - ((1 : Matrix (Fin n) (Fin n) γ) - J) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply, hJ i j]
    ring
  rw [hneg, Matrix.det_neg]
  rw [Matrix.det_one_sub_mul_comm (A := Matrix.replicateCol (Fin 1) u) (B := Matrix.replicateRow (Fin 1) u)]
  have h1 : Matrix.det ((1 : Matrix (Fin 1) (Fin 1) γ) -
      Matrix.replicateRow (Fin 1) u * Matrix.replicateCol (Fin 1) u) =
      1 - (n : γ) := by
    simp [Matrix.replicateRow_mul_replicateCol_apply, dotProduct, u, Finset.sum_const]
  rw [h1]
  have hn : n = (n - 1) + 1 := by omega
  rw [hn]
  simp [pow_succ]


/--
`det ([i < n] [j < n] if i = j then 0 else 1) = (-1)^(n-1) * (n - 1)`:
tensor form of the determinant of the all-ones matrix minus the identity.
-/
@[main]
private lemma main
  [CommRing β] (n : ℕ) (h : 0 < n) :
-- imply
  ([i < n] [j < n] (if i = j then (0 : β) else 1 : Tensor β [])).det =
    (↑((-1 : β) ^ (n - 1) * ↑(n - 1)) : Tensor β []) := by
-- proof
  let X : Tensor β [n, n] :=
    [i < n] [j < n] (if i = j then (0 : β) else 1 : Tensor β [])
  have hM : X.toMatrix = fun i j : Fin n => if i = j then (0 : Tensor β []) else 1 := by
    ext i j
    simp [Tensor.toMatrix]
    have hi := EqGetStack.fin
      (fun i : Fin n => [j < n] (if i = j then (0 : β) else 1 : Tensor β [])) i
    have hj := EqGetStack.fin
      (fun j : Fin n => (if i = j then (0 : β) else 1 : Tensor β [])) j
    simp [GetElem.getElem] at hi hj ⊢
    erw [hi, hj]
    split_ifs <;> rfl
  have hdet := det_ite (Tensor β []) n h
  rw [Det.eq.DetToMatrix X, hM, hdet]
  have hneg1 : (-1 : Tensor β []) = ↑(-1 : β) := by
    apply Eq.of.EqDataS
    exact Subtype.ext (by
      show List.map Neg.neg (List.replicate 1 (1 : β)) = [-1]
      simp)
  have hpow : (-1 : Tensor β []) ^ (n - 1) = ↑((-1 : β) ^ (n - 1)) := by
    rw [hneg1, Pow.eq.TensorListPow]
  have hcoemul : ∀ (x y : β), (↑x : Tensor β []) * ↑y = ↑(x * y) := by
    intro x y
    apply Eq.of.EqDataS
    exact Subtype.ext (by
      show List.map (fun z => Mul.mul z y) [x] = [Mul.mul x y]
      rfl)
  rw [hpow]
  exact hcoemul ((-1 : β) ^ (n - 1)) (↑(n - 1))


-- created on 2026-09-12
