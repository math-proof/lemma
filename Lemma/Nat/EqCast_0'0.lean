import sympy.Basic


@[main]
private lemma main
  [AddMonoidWithOne R] :
-- imply
  (Nat.cast (R := R) 0) = 0 :=
-- proof
  Nat.cast_zero


-- created on 2025-06-08
