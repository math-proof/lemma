import sympy.functions.elementary.exponential
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ} :
-- imply
  exp (a + b) = exp a * exp b :=
-- proof
  Real.exp_add a b


@[main]
private lemma complex
  {a b : ℂ} :
-- imply
  (a + b).exp = a.exp * b.exp :=
-- proof
  Complex.exp_add a b

-- created on 2025-01-05
