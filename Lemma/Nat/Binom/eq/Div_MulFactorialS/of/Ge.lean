import sympy.functions.combinatorial.factorials
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
-- given
  (h : n ≥ k) :
-- imply
  n.choose k = n ! / (k ! * (n - k) !) :=
-- proof
  Nat.choose_eq_factorial_div_factorial h


-- created on 2020-02-23
