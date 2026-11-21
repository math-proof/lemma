import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


@[path]
private lemma main
  [One α] :
-- imply
  (1 : List.Vector α n) = List.Vector.replicate n 1 :=
-- proof
  rfl


-- created on 2025-09-22
-- updated on 2026-11-20
