import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
attribute [local instance] Classical.decEq

/-!
# Supersingular elliptic curves

This file defines supersingularity over an algebraic closure of `ZMod p` through trivial geometric
`p`-torsion and relates it to trivial geometric `p ^ r`-torsion for every positive `r`.
-/


namespace WeierstrassCurve.Affine

/-- An elliptic curve over an algebraic closure of `ZMod p` is supersingular when every geometric
point killed by `p` is zero.

This is the `r = 1` form of the equivalent torsion condition in arXiv:2308.11539v1,
`main.tex`, lines 164–170.
-/
def IsSupersingular {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic] : Prop :=
  ∀ P : W.Point, p • P = 0 → P = 0

end WeierstrassCurve.Affine
