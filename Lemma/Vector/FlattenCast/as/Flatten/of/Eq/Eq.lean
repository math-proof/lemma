import Def.Data.Vector.Basic
import Theorem.Logic.SEq
import Instance.Data.Vector.Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.FlattenCast.as.Flatten.of.Eq.Eq |
| comm 3 | Vector.Flatten.as.FlattenCast.of.Eq.Eq |
| cast | Vector.FlattenCast.eq.Cast_Flatten.of.Eq.Eq |
-/
@[path, comm 3, cast]
private lemma main
-- given
  (h_m : m = m')
  (h_n : n = n')
  (v : List.Vector (List.Vector α n) m) :
-- imply
  (cast (congrArg₂ (fun n m => List.Vector (List.Vector α n) m) h_n h_m) v).flatten ≃ v.flatten := by
-- proof
  subst h_m h_n
  rfl


-- created on 2025-10-17
-- updated on 2026-11-20
