import sympy.functions.elementary.exponential


@[path]
private lemma main
  [LogPos α]
-- given
  (x : α) :
-- imply
  log (exp x) = x :=
-- proof
  LogPos.log_exp x


-- created on 2025-12-04
