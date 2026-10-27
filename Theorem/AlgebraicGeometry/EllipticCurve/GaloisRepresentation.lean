import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.Module.Torsion.Basic
import Def.AlgebraicGeometry.EllipticCurve.GaloisRepresentation
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

/-- The bridge preserves multiplication definitionally. -/
@[simp] theorem galAlgEquiv_mul (σ τ : Field.absoluteGaloisGroup ℚ) :
    galAlgEquiv (σ * τ) = galAlgEquiv σ * galAlgEquiv τ := rfl

/-- The bridge preserves inverses definitionally. -/
theorem galAlgEquiv_inv (σ : Field.absoluteGaloisGroup ℚ) :
    galAlgEquiv σ⁻¹ = (galAlgEquiv σ)⁻¹ := rfl

/-- The algebra-homomorphism form of the bridge is multiplicative. -/
theorem galToAlgHom_comp (σ τ : Field.absoluteGaloisGroup ℚ) :
    (galAlgEquiv (σ * τ)).toAlgHom =
      (galAlgEquiv σ).toAlgHom.comp (galAlgEquiv τ).toAlgHom := by
  ext x
  change (galAlgEquiv (σ * τ)) x = _
  rw [galAlgEquiv_mul, AlgEquiv.mul_apply]
  rfl

/-- The identity automorphism acts trivially on points. -/
theorem galPointHom_apply_one (P : Affine.Point (W.baseChange (AlgebraicClosure ℚ))) :
    galPointHom W 1 P = P := by
  cases P <;> rfl

/-- The point action is multiplicative. -/
theorem galPointHom_apply_mul (σ τ : Field.absoluteGaloisGroup ℚ)
    (P : Affine.Point (W.baseChange (AlgebraicClosure ℚ))) :
    galPointHom W (σ * τ) P = galPointHom W σ (galPointHom W τ P) := by
  change Affine.Point.map _ P = Affine.Point.map _ (Affine.Point.map _ P)
  rw [galToAlgHom_comp, ← Affine.Point.map_map]

end MetaMathlibExt
