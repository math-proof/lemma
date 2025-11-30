import sympy.Basic
import sympy.vector.Basic


@[main]
private lemma main
  [Add α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x + a)[i] = x[i] + a := by
-- proof
  simp [HAdd.hAdd]


@[main]
private lemma fin
  [Add α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x + a).get i = x.get i + a := by
-- proof
  apply main


-- created on 2025-11-30
