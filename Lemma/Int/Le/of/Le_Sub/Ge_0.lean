import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  [AddGroup α]
  [AddLeftMono α]
  {a b c : α}
-- given
  (hc : 0 ≤ c)
  (h : a ≤ b - c) :
-- imply
  a ≤ b :=
-- proof
  le_trans h (sub_le_self b hc)


-- created on 2026-09-17
