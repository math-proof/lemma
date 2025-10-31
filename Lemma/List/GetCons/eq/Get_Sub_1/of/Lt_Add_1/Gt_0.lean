import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {tail : List α}
-- given
  (h₂ : i > 0)
  (h₀ : i < tail.length + 1)
  (head : α) :
-- imply
  (head :: tail)[i] = tail[i - 1] := by
-- proof
  grind


-- created on 2025-05-15
