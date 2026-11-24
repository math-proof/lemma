module
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
public import Theorem.Scheme.EllipticCurve.ManinTwistCharTwo
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic.NormNum
public import Theorem.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- A supersingular characteristic-two curve in Manin normal form. -/
def supersingularCurve : WeierstrassCurve (ZMod 2) :=
  ⟨0, 0, 1, 0, 0⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
