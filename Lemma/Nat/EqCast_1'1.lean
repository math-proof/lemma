import sympy.Basic


@[main]
private lemma main
  [AddMonoidWithOne R] :
-- imply
  Nat.cast (R := R) 1 = 1 :=
-- proof
  Nat.cast_one


-- created on 2025-06-08
