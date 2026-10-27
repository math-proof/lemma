import Theorem.Logic.SEq
import Def.Data.Holor.Defs.Part4


@[path, fin, cast, cast.fin]
private lemma main
-- given
  (h : s = s')
  (v : List.Vector (Tensor α s) n)
  (i : Fin n) :
-- imply
  (cast (congrArg (fun s => List.Vector (Tensor α s) n) h) v)[i] ≃ v[i] := by
-- proof
  aesop


-- created on 2025-06-29
-- updated on 2026-10-26
