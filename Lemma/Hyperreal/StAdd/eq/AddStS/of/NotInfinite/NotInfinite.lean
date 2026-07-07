import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (h_a : ¬x → ∞)
  (h_b : ¬y → ∞) :
-- imply
  stdPart (x + y) = stdPart x + stdPart y :=
-- proof
  ArchimedeanClass.stdPart_add (not_lt.mp h_a) (not_lt.mp h_b)


-- created on 2025-12-10
