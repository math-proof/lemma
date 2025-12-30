import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (i : Fin n) :
-- imply
  (List.Vector.range n)[i.val] = i := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.range]
  simp [List.Vector.get]


@[main]
private lemma fin
  {n : ℕ}
-- given
  (i : Fin n) :
-- imply
  (List.Vector.range n).get i = i :=
-- proof
  main i


-- created on 2025-05-18
