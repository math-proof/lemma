import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount
open WeierstrassCurve


namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

/--
[equation_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma equation_iff (xy : ZMod 5 × ZMod 5) :
  curve.Equation xy.1 xy.2 ↔ xy.2 ^ 2 = xy.1 ^ 3 + 1 := by
  rw [WeierstrassCurve.Affine.Equation, curve.evalEval_polynomial]
  simp [curve, sub_eq_zero]

end WeierstrassCurve.Affine.PointCountTest.ZModFive

namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

/--
[natCard_affineSolutions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma natCard_affineSolutions :
  Nat.card {xy : ZMod 5 × ZMod 5 // curve.Equation xy.1 xy.2} = 5 := by
  rw [Nat.card_congr (Equiv.subtypeEquivProp (funext fun xy => propext (equation_iff xy))),
    Nat.card_eq_fintype_card]
  decide

end WeierstrassCurve.Affine.PointCountTest.ZModFive


-- created on 2026-10-23
