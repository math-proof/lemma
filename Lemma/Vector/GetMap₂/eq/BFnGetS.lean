import sympy.Basic
import sympy.vector.Basic


@[main, fin]
private lemma main
-- given
  (a : List.Vector α n)
  (b : List.Vector β n)
  (f : α → β → γ)
  (i : Fin n) :
-- imply
  (a.map₂ f b)[i] = f a[i] b[i] := by
-- proof
  simp [GetElem.getElem]


-- created on 2026-05-03
