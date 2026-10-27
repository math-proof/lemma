import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.Module.Torsion.Basic
import Def.AlgebraicGeometry.EllipticCurve.GaloisRepresentation.Part3
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

/-- The linear map acts pointwise as the point action. -/
theorem galLinearMap_apply (σ : Field.absoluteGaloisGroup ℚ)
    (x : torsionPts W p) :
    galLinearMap W p σ x = ⟨galPointHom W σ x.val, galPointHom_mem W p σ x.property⟩ :=
  rfl

/-- The identity acts as the identity linear map. -/
theorem galLinearMap_one_apply (x : torsionPts W p) :
    galLinearMap W p 1 x = x := by
  apply Subtype.ext
  change galPointHom W 1 x.val = x.val
  exact galPointHom_apply_one W x.val

/-- The linear action is multiplicative. -/
theorem galLinearMap_mul_apply (σ τ : Field.absoluteGaloisGroup ℚ)
    (x : torsionPts W p) :
    galLinearMap W p (σ * τ) x = galLinearMap W p σ (galLinearMap W p τ x) := by
  apply Subtype.ext
  change galPointHom W (σ * τ) x.val = galPointHom W σ (galPointHom W τ x.val)
  exact galPointHom_apply_mul W σ τ x.val

/-- Each Galois automorphism acts bijectively. -/
theorem galLinearMap_bijective (σ : Field.absoluteGaloisGroup ℚ) :
    Function.Bijective (galLinearMap W p σ) := by
  have hleft : Function.LeftInverse (galLinearMap W p σ⁻¹) (galLinearMap W p σ) := by
    intro x
    rw [← galLinearMap_mul_apply, inv_mul_cancel, galLinearMap_one_apply]
  have hright : Function.RightInverse (galLinearMap W p σ⁻¹) (galLinearMap W p σ) := by
    intro x
    rw [← galLinearMap_mul_apply, mul_inv_cancel, galLinearMap_one_apply]
  exact ⟨hleft.injective, hright.surjective⟩

end MetaMathlibExt
