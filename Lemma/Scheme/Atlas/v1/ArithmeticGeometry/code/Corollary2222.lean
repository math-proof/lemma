import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RiemannRoch
open RiemannRochSpace CurveDivisor CurveWithOrd


namespace Corollary2222

/--
[ell_eq_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary2222.lean)
-/
@[path]
lemma ell_eq_genus
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {W : CurveDivisor C}
-- given
  (hW : IsCanonicalDivisor W) :
-- imply
  (divisorDim (F := F) (k := k) W : ℤ) = (genus (C := C) (F := F) (k := k) : ℤ) :=
-- proof
  canonical_divisorDim_eq_genus W hW

end Corollary2222


-- created on 2026-10-23
