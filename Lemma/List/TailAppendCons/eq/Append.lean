import sympy.Basic


@[path]
private lemma main
-- given
  (x : α)
  (a b : List α) :
-- imply
  ((x :: a) ++ b).tail = a ++ b := by
-- proof
  simp


-- created on 2025-07-05
