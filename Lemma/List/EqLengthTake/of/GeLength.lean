import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {s : List α}
  {n : ℕ}
-- given
  (h : s.length ≥ n) :
-- imply
  (s.take n).length = n := by
-- proof
  grind [List.take]


-- created on 2024-07-01
-- updated on 2026-10-26
