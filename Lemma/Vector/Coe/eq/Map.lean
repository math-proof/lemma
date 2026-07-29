import sympy.vector.Basic
import sympy.Basic


@[main]
private lemma main
  [Coe α β]
-- given
  (v : List.Vector α n) :
-- imply
  (v : List.Vector β n) = v.map Coe.coe := by
-- proof
  rfl


-- created on 2026-07-28
