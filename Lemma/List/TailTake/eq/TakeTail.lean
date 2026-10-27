import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (s : List α)
  (i : ℕ):
-- imply
  (s.take (i + 1)).tail = s.tail.take i := by
-- proof
  cases s <;>
    cases i <;>
      simp [List.take, List.tail]


-- created on 2025-06-17
-- updated on 2026-10-26
