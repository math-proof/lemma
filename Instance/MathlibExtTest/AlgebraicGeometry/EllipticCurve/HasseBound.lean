/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/HasseBound.lean -/

import Lemma.Scheme.EllipticCurve.HasseBound
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound
