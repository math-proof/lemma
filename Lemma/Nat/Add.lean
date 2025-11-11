import sympy.Basic


@[main]
private lemma comm'
  [AddCommMagma α]
-- given
  (a b : α) :
-- imply
  a + b = b + a :=
-- proof
  add_comm a b


-- created on 2024-07-01
-- updated on 2025-04-04
