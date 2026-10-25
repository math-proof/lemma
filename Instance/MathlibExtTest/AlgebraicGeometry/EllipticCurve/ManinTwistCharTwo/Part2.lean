/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/

import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
import Lemma.Scheme.EllipticCurve.ManinTwistCharTwo
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum
import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : ordinaryCurve.IsCharTwoJNeZeroNF := ⟨rfl, rfl, rfl⟩

instance : ordinaryCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [ordinaryCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    isUnit_iff_ne_zero]
  decide

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
