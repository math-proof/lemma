import sympy.Basic


@[main]
private lemma comm'
  {a b : Set α} :
-- imply
  a ∩ b = b ∩ a :=
-- proof
  Set.inter_comm a b


@[main]
private lemma comm.fin
  [DecidableEq α]
  {a b : Finset α} :
-- imply
  a ∩ b = b ∩ a :=
-- proof
  Finset.inter_comm a b

-- created on 2025-06-06
