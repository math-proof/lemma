import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.Module.Torsion.Basic
import Theorem.AlgebraicGeometry.EllipticCurve.GaloisRepresentation.Part2
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

/-- The Galois action restricted to the `p`-torsion subtype. -/
noncomputable def galTorsionHom (σ : Field.absoluteGaloisGroup ℚ) :
    torsionPts W p →+ torsionPts W p where
  toFun x := ⟨galPointHom W σ x.val, galPointHom_mem W p σ x.property⟩
  map_zero' := by
    apply Subtype.ext
    change galPointHom W σ _ = _
    exact map_zero _
  map_add' := fun x y => by
    apply Subtype.ext
    change galPointHom W σ _ = _
    exact map_add _ _ _

/-- The restricted action as a `ZMod p`-linear map. -/
noncomputable def galLinearMap (σ : Field.absoluteGaloisGroup ℚ) :
    torsionPts W p →ₗ[ZMod p] torsionPts W p :=
  (galTorsionHom W p σ).toZModLinearMap p

end MetaMathlibExt
