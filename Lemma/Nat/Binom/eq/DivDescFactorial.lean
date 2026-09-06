import Mathlib.Data.Nat.Choose.Basic
import sympy.functions.combinatorial.factorials
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ} :
-- imply
  n.choose k = n.descFactorial k / k ! :=
-- proof
  Nat.choose_eq_descFactorial_div_factorial n k


-- created on 2020-02-28
