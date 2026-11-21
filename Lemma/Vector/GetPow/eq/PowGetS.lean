import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetPow.eq.PowGetS |
| fin | Vector.GetPow.eq.PowGetS.fin |
-/
@[path, fin]
private lemma main
  [HPow α β α]
-- given
  (a : List.Vector α n)
  (b : List.Vector β n)
  (i : Fin n) :
-- imply
  (a ^ b)[i] = a[i] ^ b[i] := by
-- proof
  simp [HPow.hPow, GetElem.getElem]


-- created on 2026-08-23
-- updated on 2026-11-20
