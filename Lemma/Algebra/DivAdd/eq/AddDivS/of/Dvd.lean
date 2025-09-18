import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma left
  [IntegerRing Z]
  {a b c : Z}
-- given
  (h : c ∣ b) :
-- imply
  (a + b) / c = a / c + b / c :=
-- proof
  IntegerRing.add_div_of_dvd_left h


@[main]
private lemma main
  [IntegerRing Z]
  {a b c : Z}
-- given
  (h : c ∣ a) :
-- imply
  (a + b) / c = a / c + b / c :=
-- proof
  IntegerRing.add_div_of_dvd_right h


-- created on 2025-07-08
