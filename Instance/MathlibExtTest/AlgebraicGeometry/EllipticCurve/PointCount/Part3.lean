/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Abbrev.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount


namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

instance : Fintype AffineSolution :=
  Fintype.subtype (Finset.univ.filter fun xy : ZMod 5 × ZMod 5 => xy.2 ^ 2 = xy.1 ^ 3 + 1)
    (by simp)

end WeierstrassCurve.Affine.PointCountTest.ZModFive
