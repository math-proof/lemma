import sympy.Basic


@[main]
private lemma main
  {a b : List α}
-- given
  (h₀ : i ≥ a.length)
  (h₁ : i < (a ++ b).length) :
-- imply
  have : i < a.length + b.length := by rwa [List.length_append] at h₁
  (a ++ b)[i] = b[i - a.length] := by
-- proof
  simp_all


-- created on 2025-05-15
-- updated on 2025-05-16
