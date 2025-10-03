import sympy.Basic


@[main]
private lemma main
  {a b : List α}
-- given
  (h₀ : b.length > 0) :
-- imply
  have : a.length < (a ++ b).length := by
    rw [List.length_append]
    simp_all
  (a ++ b)[a.length] = b[0] := by
-- proof
  simp_all


-- created on 2025-05-16
