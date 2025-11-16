import sympy.Basic
import sympy.functions.elementary.integers


/--
the division algorithm for any integers n and d
-/
@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n d : Z) :
-- imply
  d * (n / d) + n % d = n :=
-- proof
  IntegerRing.div_add_mod n d


-- created on 2025-11-16
