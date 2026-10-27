import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.Module.Torsion.Basic
import Theorem.AlgebraicGeometry.EllipticCurve.GaloisRepresentation.Part3
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

/-- The invertible `ZMod p`-linear action of a Galois automorphism on `E[p]`. -/
noncomputable def galLinearEquiv (σ : Field.absoluteGaloisGroup ℚ) :
    torsionPts W p ≃ₗ[ZMod p] torsionPts W p :=
  LinearEquiv.ofBijective _ (galLinearMap_bijective W p σ)

/-- The mod-`p` Galois representation `ρ_{E,p}` as a monoid homomorphism. -/
noncomputable def galRep :
    Field.absoluteGaloisGroup ℚ →* (torsionPts W p ≃ₗ[ZMod p] torsionPts W p) where
  toFun σ := galLinearEquiv W p σ
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change galLinearMap W p 1 x = _
    rw [galLinearMap_one_apply]
    rfl
  map_mul' := fun σ τ => by
    apply LinearEquiv.ext
    intro x
    change galLinearMap W p (σ * τ) x = _
    rw [galLinearMap_mul_apply]
    rfl

/-- The determinant of the mod-`p` representation. -/
noncomputable def galDetHom :
    Field.absoluteGaloisGroup ℚ →* (ZMod p)ˣ :=
  LinearEquiv.det.comp (galRep W p)

end MetaMathlibExt
