/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/

import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
import Lemma.Scheme.EllipticCurve.ManinTwist
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : curve.IsCharNeTwoNF := ⟨rfl, rfl⟩

instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, isUnit_iff_ne_zero]
  decide

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist
