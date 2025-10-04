import sympy.functions.elementary.exponential
import sympy.Basic


@[main]
private lemma main
  [ExpNeZero α]
-- given
  (x : α) :
-- imply
  exp x ≠ 0 :=
-- proof
  ExpNeZero.exp_ne_zero x


-- created on 2025-10-04
