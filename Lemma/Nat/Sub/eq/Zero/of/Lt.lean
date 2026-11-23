import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (h : a < b) :
-- imply
  a - b = 0 := by
-- proof
  apply Nat.sub_eq_zero_of_le (le_of_lt h)


-- created on 2025-05-14
-- updated on 2026-11-23
