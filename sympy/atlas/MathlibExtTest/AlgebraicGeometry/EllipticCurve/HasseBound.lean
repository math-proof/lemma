/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/HasseBound.lean -/

import Lemma.Scheme.EllipticCurve.HasseBound
import Mathlib.Algebra.Field.ZMod

import Mathlib.Tactic.NormNum

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound

open WeierstrassCurve
open MathlibExt.AlgebraicGeometry.EllipticCurve

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private def curve : WeierstrassCurve (ZMod 2) :=
  ⟨1, 0, 0, 0, 1⟩

private instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    isUnit_iff_ne_zero]
  decide

/-- The general Hasse theorem applies to an explicit characteristic-two elliptic curve. -/
example :
    (((Nat.card (ZMod 2) : ℤ) + 1 -
        (Nat.card curve.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card (ZMod 2) : ℤ)) :=
  HasseBoundWanted.hasse_bound curve

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound
