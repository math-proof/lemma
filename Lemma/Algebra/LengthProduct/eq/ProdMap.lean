import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List (List α)) :
-- imply
  (itertools.product s).length = (s.map List.length).prod := by
-- proof
  unfold itertools.product
  induction s <;>
    simp_all [List.foldr]


-- created on 2025-06-11
-- updated on 2025-06-12
