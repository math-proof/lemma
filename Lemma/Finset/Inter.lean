import sympy.Basic


@[main]
private lemma Comm
  [DecidableEq α]
  {a b : Finset α} :
-- imply
  a ∩ b = b ∩ a :=
-- proof
  Finset.inter_comm a b


-- created on 2025-12-30
