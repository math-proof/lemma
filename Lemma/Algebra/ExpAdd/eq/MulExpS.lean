import sympy.functions.elementary.exponential
import sympy.Basic


@[main]
private lemma main
  [Exp R]
  {a b : R} :
-- imply
  exp (a + b) = exp a * exp b :=
-- proof
  Exp.exp_add a b


-- created on 2025-01-05
