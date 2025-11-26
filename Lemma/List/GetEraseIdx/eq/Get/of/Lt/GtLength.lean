import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h₀ : j < s.length)
  (h₁ : i < j) :
-- imply
  (s.eraseIdx i)[j - 1]'(by grind) = s[j] := by
-- proof
  grind


-- created on 2025-11-26
