/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/

import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
import Lemma.Scheme.EllipticCurve.ManinTwistCharTwo
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
