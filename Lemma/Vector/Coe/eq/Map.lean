import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


@[path]
private lemma main
  [Coe α β]
-- given
  (v : List.Vector α n) :
-- imply
  (v : List.Vector β n) = v.map Coe.coe := by
-- proof
  rfl


-- created on 2026-07-28
-- updated on 2026-11-20
