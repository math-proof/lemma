import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma fin
  {n : ℕ}
-- given
  (i : Fin n) :
-- imply
  (List.Vector.range n).get i = i := by
-- proof
  simp [List.Vector.range]
  simp [List.Vector.get]


@[main]
private lemma main
  {n : ℕ}
-- given
  (i : Fin n) :
-- imply
  (List.Vector.range n)[i] = i :=
-- proof
  fin i


-- created on 2025-05-18
