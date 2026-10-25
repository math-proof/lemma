/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/HasseBound.lean -/

import Lemma.Scheme.EllipticCurve.HasseBound
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

def curve : WeierstrassCurve (ZMod 2) :=
  ⟨1, 0, 0, 0, 1⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound
