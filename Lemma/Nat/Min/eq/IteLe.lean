import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b = if a ≤ b then
    a
  else
    b :=
-- proof
  min_def a b


-- created on 2025-05-07
