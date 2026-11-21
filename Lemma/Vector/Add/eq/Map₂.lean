import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


@[path]
private lemma main
  [Add α]
-- given
  (a b : List.Vector α n) :
-- imply
  a + b = a.map₂ HAdd.hAdd b :=
-- proof
  rfl


-- created on 2025-06-22
-- updated on 2026-11-20
