import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetMul.eq.MulGetS |
| fin | Vector.GetMul.eq.MulGetS.fin |
-/
@[path, fin]
private lemma main
  [Mul α]
-- given
  (a b : List.Vector α n)
  (i : Fin n):
-- imply
  (a * b)[i] = a[i] * b[i] := by
-- proof
  conv in a * b =>
    simp [HMul.hMul]
  simp [Mul.mul]
  simp [GetElem.getElem]


-- created on 2025-07-14
-- updated on 2026-11-20
