module
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
public import Theorem.Scheme.EllipticCurve.ManinTwist
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist
