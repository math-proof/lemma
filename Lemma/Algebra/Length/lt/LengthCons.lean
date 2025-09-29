import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
-- given
  (head : α)
  (tail : List α) :
-- imply
  tail.length < (head :: tail).length := by
-- proof
  simp


-- created on 2025-06-02
