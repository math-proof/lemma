import sympy.Basic
import sympy.functions.elementary.integers


@[main]
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
-- updated on 2025-10-16
