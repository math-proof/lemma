import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h₀ : j + 1 < s.length)
  (h₁ : i ≤ j) :
-- imply
  (s.eraseIdx i)[j]'(by grind) = s[j + 1] := by
-- proof
  grind


-- created on 2025-11-17
-- updated on 2025-11-26
