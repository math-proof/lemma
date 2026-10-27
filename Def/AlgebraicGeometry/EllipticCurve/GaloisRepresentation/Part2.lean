import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.Module.Torsion.Basic
import Theorem.AlgebraicGeometry.EllipticCurve.GaloisRepresentation
attribute [local instance] Classical.decEq

/-!
# Galois action on `p`-torsion of an elliptic curve over `ℚ`

Infrastructure for the determinant identity of Gonzalez-Jimenez–Lozano-Robledo,
*Elliptic Curves with abelian division fields*, arXiv:1511.08578v2,
Math. Z. 283 (2016), DOI `10.1007/s00209-016-1623-z`.
-/


namespace MetaMathlibExt

open WeierstrassCurve

variable (W : Affine ℚ)

variable (p : ℕ)

/-- The `p`-torsion subgroup of the base-changed affine point group. -/
noncomputable def torsionPts :=
  AddSubgroup.torsionBy (Affine.Point (W.baseChange (AlgebraicClosure ℚ))) (p : ℤ)

end MetaMathlibExt
