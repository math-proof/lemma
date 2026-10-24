import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.PowerSeriesUFD
open PowerSeriesUFD


namespace PowerSeriesUFD

/--
[maximalIdeal_eq_span_X'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PowerSeriesUFD.lean)
-/
@[path]
lemma maximalIdeal_eq_span_X'
  {k : Type*}
  [Field k] :
-- imply
  IsLocalRing.maximalIdeal (PowerSeries k) = Ideal.span {(PowerSeries.X : PowerSeries k)} :=
-- proof
  PowerSeries.maximalIdeal_eq_span_X

end PowerSeriesUFD


-- created on 2026-10-23
