import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.Lemma2112
open RiemannRochSpace Lemma2112
open CurveWithOrd CurveDivisor


namespace Lemma2112

/--
[ell_eq_one_iff_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma2112.lean)
-/
@[path]
lemma ell_eq_one_iff_principal
  {D : CurveDivisor C}
-- given
  (hdeg : degree C D = 0) :
-- imply
  divisorDim (F := F) (k := k) D = 1 ↔ IsPrincipal (F := F) D :=
-- proof
  divisorDim_degree_zero_iff (F := F) (k := k) D hdeg

end Lemma2112


-- created on 2026-10-23
