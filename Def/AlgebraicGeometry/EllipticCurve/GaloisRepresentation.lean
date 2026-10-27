import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.Module.Torsion.Basic
attribute [local instance] Classical.decEq

/-!
# Galois action on `p`-torsion of an elliptic curve over `ℚ`

Infrastructure for the determinant identity of Gonzalez-Jimenez–Lozano-Robledo,
*Elliptic Curves with abelian division fields*, arXiv:1511.08578v2,
Math. Z. 283 (2016), DOI `10.1007/s00209-016-1623-z`.
-/


namespace MetaMathlibExt

open WeierstrassCurve

/-- An element of the absolute Galois group of `ℚ` viewed as an algebra
equivalence of the algebraic closure. -/
noncomputable def galAlgEquiv (σ : Field.absoluteGaloisGroup ℚ) :
    AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ

variable (W : Affine ℚ)

/-- The natural Galois action on affine nonsingular points of the base-changed
curve `W` over the algebraic closure of `ℚ`, via `Affine.Point.map`. -/
noncomputable def galPointHom (σ : Field.absoluteGaloisGroup ℚ) :
    Affine.Point (W.baseChange (AlgebraicClosure ℚ)) →+
      Affine.Point (W.baseChange (AlgebraicClosure ℚ)) :=
  Affine.Point.map (galAlgEquiv σ).toAlgHom

end MetaMathlibExt
