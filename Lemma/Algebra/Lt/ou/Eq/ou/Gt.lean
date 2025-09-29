import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a < b ∨ a = b ∨ a > b :=
-- proof
  lt_trichotomy a b


-- created on 2025-03-30
