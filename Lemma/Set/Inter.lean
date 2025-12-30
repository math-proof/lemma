import sympy.Basic


@[main]
private lemma Comm
  {a b : Set α} :
-- imply
  a ∩ b = b ∩ a :=
-- proof
  Set.inter_comm a b


-- created on 2025-06-06
