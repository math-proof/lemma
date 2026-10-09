import sympy.Basic


@[path, comm]
private lemma main
-- given
  (s : List α) :
-- imply
  s.dropLast = s.take (s.length - 1) := by
-- proof
  apply List.dropLast_eq_take


-- created on 2025-11-24
