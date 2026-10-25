import Mathlib
import sympy.Basic
import Lemma.ModularCurve.X1


/-- ported from external source -/
@[path]
private lemma main
  [Field L] [CharZero L] :
-- imply
  ModularCurve.coeffEmb L ModularCurve.jq ≠ 0 :=
-- proof
  (map_ne_zero (ModularCurve.coeffEmb L)).mpr ModularCurve.jq_ne_zero


-- created on 2026-10-23
