import sympy.functions.elementary.exponential
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.ExpAdd.eq.MulExpS |
| comm | Real.MulExpS.eq.ExpAdd |
-/
@[main, comm]
private lemma main
  [Exp R]
  {a b : R} :
-- imply
  exp (a + b) = exp a * exp b :=
-- proof
  Exp.exp_add a b


-- created on 2018-08-28
-- updated on 2026-08-22

