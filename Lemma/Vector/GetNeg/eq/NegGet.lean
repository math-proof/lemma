import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetNeg.eq.NegGet |
| comm | Vector.NegGet.eq.GetNeg |
| fin | Vector.GetNeg.eq.NegGet.fin |
| fin.comm | Vector.NegGet.eq.GetNeg.fin |
-/
@[path, comm, fin, fin.comm]
private lemma main
  [Neg α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (-x)[i] = -x[i] := by
-- proof
  simp [Neg.neg]


-- created on 2025-10-04
-- updated on 2026-11-20
