/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/HasseBound.lean -/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound
