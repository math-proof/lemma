module
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
public import Theorem.Scheme.EllipticCurve.ManinTwistCharTwo
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic.NormNum
public import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : supersingularCurve.IsCharTwoJEqZeroNF := ⟨rfl, rfl⟩

instance : supersingularCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [supersingularCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    isUnit_iff_ne_zero]
  decide

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
