import sympy.Basic


@[main]
private lemma main
-- given
  (a : α)
  (b : List α) :
-- imply
  (a :: b).take 1 = [a] := by
-- proof
  simp_all


-- created on 2025-06-14
