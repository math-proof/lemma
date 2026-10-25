/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, isUnit_iff_ne_zero]
  decide

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
