/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount


namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

instance : curve.IsShortNF := ⟨rfl, rfl, rfl⟩

instance : curve.IsElliptic :=
  WeierstrassCurve.IsElliptic.mk (by
    rw [curve.Δ_of_isShortNF]
    apply isUnit_iff_ne_zero.mpr
    have h : (16 : ZMod 5) ≠ 0 ∧ (27 : ZMod 5) ≠ 0 := ⟨by decide, by decide⟩
    simpa [curve] using h)

end WeierstrassCurve.Affine.PointCountTest.ZModFive
