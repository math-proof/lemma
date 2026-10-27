import Initialize.Tactic.Attr.Basic
import Instance.Data.Int.Integers


@[path]
private lemma main
  [IntegerRing α]
  {a b c : α}
-- given
  (h : a ≥ b) :
-- imply
  c - a ≤ c - b :=
-- proof
  IntegerRing.sub_le_sub_left h


-- created on 2025-06-19
-- updated on 2026-10-26
