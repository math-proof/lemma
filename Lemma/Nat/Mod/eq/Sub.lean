import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [NeZero i]
-- given
  (n : ℕ) :
-- imply
  (n - i) % n = n - i :=
-- proof
  Nat.self_sub_mod n i


-- created on 2025-10-17
-- updated on 2026-10-26
