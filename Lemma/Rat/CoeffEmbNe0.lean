import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.X1
import Lemma.Int.P2MUtil


/--
[ModularCurve_coeffEmb_jq_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_coeffEmb_jq_ne_zero.lean)
-/
@[path]
private lemma main
  [Field L] [CharZero L] :
-- imply
  ModularCurve.coeffEmb L ModularCurve.jq ≠ 0 :=
-- proof
  (map_ne_zero (ModularCurve.coeffEmb L)).mpr ModularCurve.jq_ne_zero


-- created on 2026-10-23
