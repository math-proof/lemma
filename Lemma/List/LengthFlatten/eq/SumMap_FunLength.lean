import sympy.Basic


@[path]
private lemma main
  {s : List (List α)} :
-- imply
  s.flatten.length = (s.map fun s => s.length).sum := by
-- proof
  induction s <;> simp


-- created on 2024-07-01
