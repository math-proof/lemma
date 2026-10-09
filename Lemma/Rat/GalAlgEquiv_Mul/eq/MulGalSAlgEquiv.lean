import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.EllipticCurve.GaloisRepresentation

open MetaMathlibExt WeierstrassCurve

attribute [local instance] Classical.decEq

/--
[galAlgEquiv_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galAlgEquiv_mul_eq
-- given
  (σ τ : Field.absoluteGaloisGroup ℚ) :
-- imply
  galAlgEquiv (σ * τ) = galAlgEquiv σ * galAlgEquiv τ := by
-- proof
  apply MetaMathlibExt.galAlgEquiv_mul


/--
[galAlgEquiv_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galAlgEquiv_inv_eq
-- given
  (σ : Field.absoluteGaloisGroup ℚ) :
-- imply
  galAlgEquiv σ⁻¹ = (galAlgEquiv σ)⁻¹ := by
-- proof
  apply MetaMathlibExt.galAlgEquiv_inv


/--
[galToAlgHom_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galToAlgHom_comp_eq
-- given
  (σ τ : Field.absoluteGaloisGroup ℚ) :
-- imply
  (galAlgEquiv (σ * τ)).toAlgHom =
    (galAlgEquiv σ).toAlgHom.comp (galAlgEquiv τ).toAlgHom := by
-- proof
  apply MetaMathlibExt.galToAlgHom_comp


/--
[galPointHom_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galPointHom_apply_one_eq
-- given
  (W : Affine ℚ) (P : Affine.Point (W.baseChange (AlgebraicClosure ℚ))) :
-- imply
  galPointHom W 1 P = P := by
-- proof
  apply MetaMathlibExt.galPointHom_apply_one


/--
[galPointHom_apply_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galPointHom_apply_mul_eq
-- given
  (W : Affine ℚ) (σ τ : Field.absoluteGaloisGroup ℚ)
  (P : Affine.Point (W.baseChange (AlgebraicClosure ℚ))) :
-- imply
  galPointHom W (σ * τ) P = galPointHom W σ (galPointHom W τ P) := by
-- proof
  apply MetaMathlibExt.galPointHom_apply_mul


/--
[mem_torsionPts_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma mem_torsionPts_iff_eq
-- given
  (W : Affine ℚ) (p : ℕ)
  {x : Affine.Point (W.baseChange (AlgebraicClosure ℚ))} :
-- imply
  x ∈ torsionPts W p ↔ p • x = 0 := by
-- proof
  apply MetaMathlibExt.mem_torsionPts_iff


/--
[galPointHom_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galPointHom_mem_eq
-- given
  (W : Affine ℚ) (p : ℕ)
  {x : Affine.Point (W.baseChange (AlgebraicClosure ℚ))}
  (hx : x ∈ torsionPts W p)
  (σ : Field.absoluteGaloisGroup ℚ) :
-- imply
  galPointHom W σ x ∈ torsionPts W p := by
-- proof
  apply MetaMathlibExt.galPointHom_mem
  · exact hx


/--
[galLinearMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galLinearMap_apply_eq
-- given
  (W : Affine ℚ) (p : ℕ) (σ : Field.absoluteGaloisGroup ℚ)
  (x : torsionPts W p) :
-- imply
  galLinearMap W p σ x = ⟨galPointHom W σ x.val, galPointHom_mem W p σ x.property⟩ := by
-- proof
  apply MetaMathlibExt.galLinearMap_apply


/--
[galLinearMap_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galLinearMap_one_apply_eq
-- given
  (W : Affine ℚ) (p : ℕ) (x : torsionPts W p) :
-- imply
  galLinearMap W p 1 x = x := by
-- proof
  apply MetaMathlibExt.galLinearMap_one_apply


/--
[galLinearMap_mul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galLinearMap_mul_apply_eq
-- given
  (W : Affine ℚ) (p : ℕ) (σ τ : Field.absoluteGaloisGroup ℚ)
  (x : torsionPts W p) :
-- imply
  galLinearMap W p (σ * τ) x = galLinearMap W p σ (galLinearMap W p τ x) := by
-- proof
  apply MetaMathlibExt.galLinearMap_mul_apply


/--
[galLinearMap_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean)
-/
@[path]
private lemma galLinearMap_bijective_eq
-- given
  (W : Affine ℚ) (p : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
-- imply
  Function.Bijective (galLinearMap W p σ) := by
-- proof
  apply MetaMathlibExt.galLinearMap_bijective


-- created on 2026-10-09
