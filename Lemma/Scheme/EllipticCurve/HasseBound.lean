import Mathlib
import sympy.Basic
import sympy.atlas.AlgebraicGeometry.EllipticCurve.HasseBound
open MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted


/--
[hasse_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/HasseBound.lean)
-/
@[path]
private lemma hasse_bound_eq
  [Field F] [Fintype F] [DecidableEq F]
  {W : WeierstrassCurve F} [W.IsElliptic] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card (W.toAffine.Point) : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted.hasse_bound W


-- created on 2026-10-20
