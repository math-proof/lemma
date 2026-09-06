import Lemma.List.Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import sympy.matrices.dense
open List


/--
[torch.linalg.det](https://docs.pytorch.org/docs/stable/generated/torch.linalg.det.html)
Mirrors [sympy.det](https://github.com/sympy/sympy/blob/master/sympy/matrices/determinant.py).

Last two axes must be a square matrix `(*, n, n)`. The result has the batch shape `s.take (s.length - 2)`.
-/
def Tensor.det [CommRing α] (X : Tensor α s) : Tensor α (s.take (s.length - 2)) :=
  if h_s : s.length > 2 then
    cast
      (by
        apply congrArg (Tensor α)
        calc
          _ = s[0] :: s.tail.take (s.tail.length - 2) := by
            rw [HeadD.eq.Get_0.of.GtLength_0 (Nat.zero_lt_of_lt h_s) 1]
          _ = s[0] :: s.tail.take (s.length - 2 - 1) := by
            congr 1
            rw [length_tail, Nat.sub_sub, Nat.sub_sub]
          _ = s.take (s.length - 2) := by
            rw [← Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0 (Nat.zero_lt_of_lt h_s) (Nat.sub_pos_of_lt h_s)]
      )
      (Tensor.OfVector (X.toVector.map det))
  else if h_s : s.length < 2 then
    0
  else
    have h_len : s.length = 2 := by omega
    match h : s with
    | [m, n] =>
      if h_eq : m = n then
        (cast (by simp [h_eq]) X : Tensor α [n, n]).toMatrix.det
      else
        0
