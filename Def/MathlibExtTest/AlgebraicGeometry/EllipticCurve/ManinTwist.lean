/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/

import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
import Lemma.Scheme.EllipticCurve.ManinTwist
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Theorem.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- The test curve `y² = x³ + x + 1` over `ZMod 5`. -/
def curve : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 1⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist
