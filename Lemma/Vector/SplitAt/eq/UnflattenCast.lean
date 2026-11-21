import Def.Data.Vector.Basic.Part2
import Instance.Data.Vector.Vector
open List


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.SplitAt.eq.UnflattenCast |
| comm | Vector.UnflattenCast.eq.SplitAt |
-/
@[path, comm]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (d : ℕ) :
-- imply
  v.splitAt d = (cast (congrArg (List.Vector α) (Prod.eq.MulProdS s d)) v).unflatten := by
-- proof
  simp [List.Vector.splitAt]


-- created on 2025-07-12
-- updated on 2026-11-20
