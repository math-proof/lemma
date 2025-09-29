import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊔ b = if a ≤ b then
    b
  else
    a :=
-- proof
  max_def a b


-- created on 2025-05-07
