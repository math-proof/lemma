import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≠ 0) :
-- imply
  s = s[0] :: s.tail := by
-- proof
  cases s
  ·
    contradiction
  ·
    rfl


-- created on 2024-07-01
-- updated on 2025-06-15
