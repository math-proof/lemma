import sympy.functions.elementary.exponential
import sympy.Basic


@[main]
private lemma main
  [LogPos α]
  {x y : α}
-- given
  (h₀ : x ≠ 0)
  (h₁ : y ≠ 0) :
-- imply
  log (x * y) = log x + log y :=
-- proof
  LogPos.log_mul h₀ h₁


-- created on 2025-10-03
