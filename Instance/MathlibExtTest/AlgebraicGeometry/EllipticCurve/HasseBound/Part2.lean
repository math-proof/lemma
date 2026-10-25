/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/HasseBound.lean -/

import Lemma.Scheme.EllipticCurve.HasseBound
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    isUnit_iff_ne_zero]
  decide

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound
