import sympy.Basic


@[path]
private lemma main
  {a b : List α}
-- given
  (h₀ : a.length > i) :
-- imply
  have : i < (a ++ b).length := by
    rw [List.length_append]
    linarith
  (a ++ b)[i] = a[i] := by
-- proof
  simp_all


-- created on 2025-05-30
