import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  stdPart (-x) = -stdPart x :=
-- proof
  ArchimedeanClass.stdPart_neg x


-- created on 2025-12-16
