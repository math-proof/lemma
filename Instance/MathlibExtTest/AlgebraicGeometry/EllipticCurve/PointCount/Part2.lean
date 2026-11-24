module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/
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
