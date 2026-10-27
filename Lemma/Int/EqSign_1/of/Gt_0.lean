import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℤ}
-- given
  (h : x > 0) :
-- imply
  sign x = 1 :=
-- proof
  Int.sign_eq_one_of_pos h


-- created on 2025-03-30
-- updated on 2026-10-26
