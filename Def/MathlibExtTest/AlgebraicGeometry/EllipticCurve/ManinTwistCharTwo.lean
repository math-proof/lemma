/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/

import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
import Lemma.Scheme.EllipticCurve.ManinTwistCharTwo
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- An ordinary characteristic-two curve in Manin normal form. -/
def ordinaryCurve : WeierstrassCurve (ZMod 2) :=
  ⟨1, 0, 0, 0, 1⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
