import stdlib.List.Vector.Basic
import sympy.Basic


@[main]
private lemma main
  [Div α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x / a)[i] = x[i] / a := by
-- proof
  simp [HDiv.hDiv]


@[main]
private lemma fin
  [Div α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x / a).get i = x.get i / a := by
-- proof
  apply main


-- created on 2025-09-22
-- updated on 2025-09-23
