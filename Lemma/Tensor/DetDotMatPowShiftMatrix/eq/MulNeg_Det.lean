import Lemma.Fin.Sum_Delta.eq.Ite
import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.DetStack_Ite.eq.MulPowNeg1
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetMatPowShiftMatrix.eq.Mod
import Lemma.Tensor.GetSum.eq.Sum_Get.of.GtLength_0
import Lemma.Tensor.Mul
import Lemma.Tensor.Pow.eq.TensorListPow
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import sympy.matrices.expressions.matpow
import sympy.matrices.expressions.permutation
import sympy.tensor.stack
open Matrix Nat Tensor


@[main]
private lemma main
  [CommRing α] [CharZero α]
  (n : ℕ)
  (h : 0 < n)
  (A : Tensor α [n, n]) :
-- imply
  (∑ k ∈ Finset.Ico 1 n,
      ((ShiftMatrix (α := α) n 0 (n - 1) ^ (k : ℤ)) @ A : Tensor α [n, n])).det =
    (-1 : Tensor α []) ^ (n - 1) * (↑(n - 1) : Tensor α []) *
      id (α := Tensor α []) A.det := by
-- proof
  let S := ShiftMatrix (α := α) n 0 (n - 1)
  let P : Tensor α [n, n] := ∑ k ∈ Finset.Ico 1 n, S ^ (k : ℤ)
  let L : Tensor α [n, n] :=
    ∑ k ∈ Finset.Ico 1 n, ((S ^ (k : ℤ)) @ A : Tensor α [n, n])
  have hsum_toMatrix : ∀ (X : ℕ → Tensor α [n, n]),
      (∑ k ∈ Finset.Ico 1 n, X k).toMatrix =
        ∑ k ∈ Finset.Ico 1 n, (X k).toMatrix := by
    intro X
    apply Matrix.ext
    intro i j
    simp only [Tensor.toMatrix, GetElem.getElem]
    erw [Finset.sum_apply, Finset.sum_apply]
    simp only [Tensor.toMatrix, GetElem.getElem]
    erw [Tensor.GetSum.eq.Sum_Get.of.GtLength_0 (s := [n, n]) (by simp) X i,
      Tensor.GetSum.eq.Sum_Get.of.GtLength_0 (s := [n]) (by simp)
        (fun k => (X k).get i) j]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun x : Fin n => ((X k).get x).get j) (Fin.ext rfl)
  let f (k : ℕ) : Tensor α [n, n] := S ^ (k : ℤ)
  let g (k : ℕ) : Tensor α [n, n] := (f k) @ A
  have hL : L.toMatrix = P.toMatrix * A.toMatrix := by
    show (∑ k ∈ Finset.Ico 1 n, g k).toMatrix = _
    rw [hsum_toMatrix g, hsum_toMatrix f]
    have hm : ∑ k ∈ Finset.Ico 1 n, (g k).toMatrix =
        ∑ k ∈ Finset.Ico 1 n, (f k).toMatrix * A.toMatrix := by
      apply Finset.sum_congr rfl
      intro k _
      exact Tensor.ToMatrixDot.eq.MulToMatrixS (f k) A
    rw [hm, Matrix.sum_mul]
  let M : Matrix (Fin n) (Fin n) (Tensor α []) :=
    fun i j => ↑(if i = j then (0 : Nat) else 1)
  have hcast : ∀ (i j : Fin n),
      M i j = if i = j then (0 : Tensor α []) else 1 := by
    intro i j
    simp only [M]
    split_ifs
    · exact Nat.cast_zero
    · exact Nat.cast_one
  have hP : P.toMatrix = M := by
    ext i j
    rw [hsum_toMatrix f]
    erw [Finset.sum_apply, Finset.sum_apply]
    have hdelta : ∀ c ∈ Finset.Ico 1 n, (f c).toMatrix i j =
        (↑(KroneckerDelta (((i : ℕ) + c) % n) (j : ℕ)) : Tensor α []) := by
      intro c _
      simp only [f, Tensor.toMatrix]
      exact Tensor.GetMatPowShiftMatrix.eq.Mod n h c i j
    rw [Finset.sum_congr rfl hdelta]
    erw [← Nat.cast_sum]
    rw [Fin.Sum_Delta.eq.Ite i j]
    have hc : (↑(if i = j then (0 : Nat) else 1) : Tensor α []) =
        (if i = j then (0 : Tensor α []) else 1) := by
      split_ifs
      · exact Nat.cast_zero
      · exact Nat.cast_one
    exact hc.trans (hcast i j).symm
  have hM' : M = (fun i j : Fin n => if i = j then (0 : Tensor α []) else 1) := by
    ext i j
    exact hcast i j
  let Q : Tensor α [n, n] :=
    [i < n] [j < n] (if i = j then (0 : α) else 1 : Tensor α [])
  have hQM' : Q.toMatrix =
      (fun i j : Fin n => if i = j then (0 : Tensor α []) else 1) := by
    ext i j
    simp [Tensor.toMatrix]
    have hi := EqGetStack.fin
      (fun i : Fin n => [j < n] (if i = j then (0 : α) else 1 : Tensor α [])) i
    have hj := EqGetStack.fin
      (fun j : Fin n => (if i = j then (0 : α) else 1 : Tensor α [])) j
    simp [GetElem.getElem] at hi hj ⊢
    erw [hi, hj]
    split_ifs <;> rfl
  have hQM : Q.toMatrix = M := hQM'.trans hM'.symm
  have hqd : Q.det = M.det := by
    rw [Det.eq.DetToMatrix Q]
    exact congrArg Matrix.det hQM
  have hneg1 : (-1 : Tensor α []) = ↑(-1 : α) := by
    apply Eq.of.EqDataS
    exact Subtype.ext (by
      show List.map Neg.neg (List.replicate 1 (1 : α)) = [-1]
      simp)
  have hcoemul : ∀ (x y : α), (↑(x * y) : Tensor α []) =
      (↑x : Tensor α []) * ↑y := by
    intro x y
    apply Eq.of.EqDataS
    exact Subtype.ext (by
      show List.map (fun z => Mul.mul z y) [x] = [Mul.mul x y]
      rfl)
  have hbridge : (↑((-1 : α) ^ (n - 1) * ↑(n - 1)) : Tensor α []) =
      (-1 : Tensor α []) ^ (n - 1) * (↑(n - 1) : Tensor α []) := by
    calc (↑((-1 : α) ^ (n - 1) * ↑(n - 1)) : Tensor α [])
      = (↑((-1 : α) ^ (n - 1)) : Tensor α []) * ↑(n - 1) :=
        (hcoemul ((-1 : α) ^ (n - 1)) (↑(n - 1))).symm
    _ = ((↑(-1 : α) : Tensor α []) ^ (n - 1)) * ↑(n - 1) := by
      rw [← Pow.eq.TensorListPow (-1 : α) (n - 1)]
    _ = (-1 : Tensor α []) ^ (n - 1) * (↑(n - 1) : Tensor α []) := by
      rw [← hneg1]
  have hdetM : M.det =
      (-1 : Tensor α []) ^ (n - 1) * (↑(n - 1) : Tensor α []) :=
    hqd.symm.trans
      ((Tensor.DetStack_Ite.eq.MulPowNeg1 (β := α) n h).trans hbridge)
  have hstep1 : L.toMatrix.det = (P.toMatrix * A.toMatrix).det := by rw [hL]
  show L.det = _
  rw [Det.eq.DetToMatrix L, hstep1, Matrix.det_mul, hP, hdetM]
  rw [← Det.eq.DetToMatrix A]
  exact (Tensor.Mul _ (id (α := Tensor α []) A.det)).symm


-- created on 2020-10-03
-- updated on 2026-09-13
