import sympy.Basic


@[path, comm]
private lemma main
-- given
  (L : List (List α)) :
-- imply
  L.flatten.length = (L.map List.length).sum := by
-- proof
  apply List.length_flatten


-- created on 2025-05-08
