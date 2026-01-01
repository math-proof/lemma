import sympy.Basic
import sympy.vector.Basic


@[main, fin]
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


-- created on 2025-11-30
