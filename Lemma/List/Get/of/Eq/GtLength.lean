import sympy.Basic


@[main]
private lemma main
  {a b : List α}
  {i : ℕ}
-- given
  (h₀ : a.length > i)
  (h₁ : a = b) :
-- imply
  have : i < b.length := by simp_all
  a[i] = b[i] := by
-- proof
  simp [h₁]


-- created on 2025-05-31
