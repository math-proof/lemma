module

public import Instance.Data.Int.Integers

public section


/--
the division algorithm for any integers n and d
-/
public theorem Nat.EqAddMul_Div
  [IntegerRing Z]
-- given
  (n d : Z) :
-- imply
  d * (n / d) + n % d = n :=
-- proof
  IntegerRing.div_add_mod n d


-- created on 2025-11-16
