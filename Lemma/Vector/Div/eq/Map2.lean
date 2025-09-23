import stdlib.List.Vector.Basic
import Lemma.Basic


@[main]
private lemma main
  [Div α]
-- given
  (a b : List.Vector α n) :
-- imply
  a / b = a.map₂ HDiv.hDiv b :=
-- proof
  rfl


-- created on 2025-09-23
