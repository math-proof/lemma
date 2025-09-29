import sympy.Basic


@[main]
private lemma nat
  {a : ℕ} :
-- imply
  a - 0 = a :=
-- proof
  Nat.sub_zero a


@[main]
private lemma main
  [SubNegZeroMonoid α]
  {a : α} :
-- imply
  a - 0 = a :=
-- proof
  sub_zero a


-- created on 2025-04-11
