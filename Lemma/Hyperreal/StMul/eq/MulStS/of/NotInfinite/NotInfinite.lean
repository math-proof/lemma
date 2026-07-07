import sympy.Basic
import sympy.series.limits


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (hx : ¬x → ∞)
  (hy : ¬y → ∞) :
-- imply
  stdPart (x * y) = stdPart x * stdPart y :=
-- proof
  ArchimedeanClass.stdPart_mul (not_lt.mp hx) (not_lt.mp hy)


-- created on 2025-12-10
