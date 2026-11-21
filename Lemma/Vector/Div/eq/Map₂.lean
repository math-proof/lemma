import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


@[path]
private lemma main
  [Div α]
-- given
  (a b : List.Vector α n) :
-- imply
  a / b = a.map₂ HDiv.hDiv b :=
-- proof
  rfl


-- created on 2025-09-23
-- updated on 2026-11-20
