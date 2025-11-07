import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (head : α) 
  (tail : List α) :
-- imply
  (head :: tail)[0] = head := by
-- proof
  simp


-- created on 2025-11-07
