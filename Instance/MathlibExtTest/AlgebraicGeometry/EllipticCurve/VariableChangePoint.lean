/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
