import sympy.functions.elementary.exponential
import sympy.Basic


@[main]
private lemma main
  [LogPos α]
-- given
  (x : α) :
-- imply
  log (exp x) = x :=
-- proof
  LogPos.log_exp x


-- created on 2025-12-04
