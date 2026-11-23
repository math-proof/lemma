/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

module

public import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
public import Theorem.Scheme.EllipticCurve.VariableChangePoint
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
@[expose] public section

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
