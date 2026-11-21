import Def.Data.Vector.Basic.Part2
import Instance.Data.Vector.Vector
import Lemma.Bool.HEq.of.All_Eq.Eq.Eq
import Lemma.List.Prod.eq.Foldr
import Lemma.Bool.HEq.of.All_HEq.Eq
import Lemma.Bool.Imp_Decidable.of.Eq
open List Bool


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetSplitAt_1.eq.GetUnflatten |
| comm | Vector.GetUnflatten.eq.GetSplitAt_1 |
| fin | Vector.GetSplitAt_1.eq.GetUnflatten.fin |
| fin.comm | Vector.GetUnflatten.eq.GetSplitAt_1.fin |
-/
@[path, comm, fin, fin.comm]
private lemma main
-- given
  (v : List.Vector α (n :: s).prod)
  (i : Fin n) :
-- imply
  (v.splitAt 1)[i] = v.unflatten[i] := by
-- proof
  unfold List.Vector.splitAt
  simp [GetElem.getElem]
  congr
  ·
    simp
  ·
    simp
  .
    grind
  repeat simp


-- created on 2025-07-16
-- updated on 2026-11-20
