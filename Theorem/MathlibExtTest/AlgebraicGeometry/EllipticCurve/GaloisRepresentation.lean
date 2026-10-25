/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean -/


import sympy.atlas.AlgebraicGeometry.EllipticCurve.GaloisRepresentation
/-!
# Tests for the Galois action on `p`-torsion

Exercises the concrete production API of `GaloisRepresentation` (point action,
linear action, bijectivity, determinant character) on `E[p]`.
-/


namespace MetaMathlibExt

open WeierstrassCurve

example (W : Affine ℚ) (p : ℕ) (x : torsionPts W p) :
    galLinearMap W p 1 x = x :=
  galLinearMap_one_apply W p x

example (W : Affine ℚ) (p : ℕ) (σ τ : Field.absoluteGaloisGroup ℚ)
    (x : torsionPts W p) :
    galLinearMap W p (σ * τ) x = galLinearMap W p σ (galLinearMap W p τ x) :=
  galLinearMap_mul_apply W p σ τ x

example (W : Affine ℚ) (p : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    Function.Bijective (galLinearMap W p σ) :=
  galLinearMap_bijective W p σ

example (W : Affine ℚ) (p : ℕ) : galDetHom W p 1 = 1 :=
  map_one _

example (W : Affine ℚ) (p : ℕ) (σ : Field.absoluteGaloisGroup ℚ)
    (x : torsionPts W p) :
    galLinearMap W p σ x =
      ⟨galPointHom W σ x.val, galPointHom_mem W p σ x.property⟩ :=
  rfl

end MetaMathlibExt
