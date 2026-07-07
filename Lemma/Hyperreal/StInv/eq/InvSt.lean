import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
  [LinearOrder K] [Field K] [IsOrderedRing K]
-- given
  (x : K) :
-- imply
  stdPart x⁻¹ = (stdPart x)⁻¹ :=
-- proof
  ArchimedeanClass.stdPart_inv x


-- created on 2025-12-09
-- updated on 2025-12-10
