import sympy.Basic


@[main]
private lemma main
  {s : List α} :
-- imply
  x ∈ x :: s := by
-- proof
  apply List.Mem.head


-- created on 2024-07-01
