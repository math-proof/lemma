import sympy.Basic


@[main]
private lemma Comm
  [LinearOrder α]
  {a b : α} :
-- imply
  a ⊓ b = b ⊓ a :=
-- proof
  min_comm a b


-- created on 2025-06-06
