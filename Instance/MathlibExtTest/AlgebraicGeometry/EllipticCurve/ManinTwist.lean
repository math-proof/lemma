/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/

import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
import Lemma.Scheme.EllipticCurve.ManinTwist
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist
