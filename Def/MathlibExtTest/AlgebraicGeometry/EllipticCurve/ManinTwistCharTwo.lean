module
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
public import Theorem.Scheme.EllipticCurve.ManinTwistCharTwo
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic.NormNum
public import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- An ordinary characteristic-two curve in Manin normal form. -/
def ordinaryCurve : WeierstrassCurve (ZMod 2) :=
  ⟨1, 0, 0, 0, 1⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
