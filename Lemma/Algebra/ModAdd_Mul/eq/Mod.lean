import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (a b c : Z) :
-- imply
  (a + b * c) % c = a % c :=
-- proof
  IntegerRing.add_mul_mod_self_right a b c


@[main]
private lemma left
  [IntegerRing Z]
-- given
  (a b c : Z) :
-- imply
  (a + b * c) % b = a % b :=
-- proof
  IntegerRing.add_mul_mod_self_left a b c


-- created on 2025-07-08
