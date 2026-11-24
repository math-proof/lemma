module
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
public import Theorem.Scheme.EllipticCurve.ManinTwistCharTwo
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic.NormNum


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
