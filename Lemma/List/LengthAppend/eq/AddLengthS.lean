import sympy.Basic


@[main, comm]
private lemma main
-- given
  (a b : List α) :
-- imply
  (a ++ b).length = a.length + b.length := by
-- proof
  apply List.length_append


-- created on 2025-05-08
