import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetInv.eq.InvGet |
| comm | Vector.InvGet.eq.GetInv |
| fin | Vector.GetInv.eq.InvGet.fin |
| fin.comm | Vector.InvGet.eq.GetInv.fin |
-/
@[path, comm, fin, fin.comm]
private lemma main
  [Inv α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  x⁻¹[i] = x[i]⁻¹ := by
-- proof
  simp [Inv.inv]


-- created on 2025-09-23
-- updated on 2026-11-20
