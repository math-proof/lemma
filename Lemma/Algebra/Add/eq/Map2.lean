import stdlib.List.Vector.Basic
import Lemma.Basic


@[main]
private lemma main
  [Add α]
-- given
  (a b : List.Vector α n) :
-- imply
  a + b = a.map₂ HAdd.hAdd b :=
-- proof
  rfl


-- created on 2025-06-22
