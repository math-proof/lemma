import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {d : ℕ}
-- given
  (h : d ≠ 0)
  (n : ℕ) :
-- imply
  n % d < d := by
-- proof
  apply Nat.mod_lt n (Nat.pos_of_ne_zero h)


-- created on 2025-07-07
-- updated on 2026-11-20
