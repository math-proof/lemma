import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (s : List α)
  (n : ℕ) :
-- imply
  (s.take n).length = n ⊓ s.length := by
-- proof
  simp


-- created on 2025-05-13
-- updated on 2026-10-26
