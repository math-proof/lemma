import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.Module.Torsion.Basic
import Instance.AlgebraicGeometry.EllipticCurve.GaloisRepresentation
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

/-- Membership in `torsionPts` is the `p`-torsion condition. -/
theorem mem_torsionPts_iff {x : Affine.Point (W.baseChange (AlgebraicClosure ℚ))} :
    x ∈ torsionPts W p ↔ p • x = 0 := by
  change x ∈ AddSubgroup.torsionBy _ _ ↔ _
  exact AddSubgroup.torsionBy.nsmul_iff

/-- The Galois point action preserves `p`-torsion. -/
theorem galPointHom_mem (σ : Field.absoluteGaloisGroup ℚ)
    {x : Affine.Point (W.baseChange (AlgebraicClosure ℚ))}
    (hx : x ∈ torsionPts W p) : galPointHom W σ x ∈ torsionPts W p := by
  rw [mem_torsionPts_iff] at hx ⊢
  rw [← map_nsmul]
  rw [hx, map_zero]

end MetaMathlibExt
