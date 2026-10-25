/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Theorem.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount


namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

end WeierstrassCurve.Affine.PointCountTest.ZModFive
