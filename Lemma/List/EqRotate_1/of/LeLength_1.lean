import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≤ 1) :
-- imply
  s.rotate 1 = s := by
-- proof
  cases s <;>
    aesop

-- created on 2025-10-20
