import Mathlib
import sympy.Basic
open AlgebraicGeometry CategoryTheory


/--
[lemma27_affine_morphism_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec13AffineMorphisms.lean)
-/
@[path]
lemma lemma27_affine_morphism_iff
  {X Y : Scheme}
  {f : X ⟶ Y} :
-- imply
  IsAffineHom f ↔ ∀ (U : Y.Opens), IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U) :=
-- proof
  isAffineHom_iff f

/--
[lemma27_affine_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec13AffineMorphisms.lean)
-/
@[path]
lemma lemma27_affine_preimage
  {X Y : Scheme}
  {f : X ⟶ Y}
  [IsAffineHom f]
  {U : Y.Opens}
-- given
  (hU : IsAffineOpen U) :
-- imply
  IsAffineOpen (f ⁻¹ᵁ U) :=
-- proof
  (isAffineHom_iff f).mp inferInstance U hU

/--
[lemma27_affineHom_of_preimages_affine](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec13AffineMorphisms.lean)
-/
@[path]
lemma lemma27_affineHom_of_preimages_affine
  {X Y : Scheme}
  {f : X ⟶ Y}
-- given
  (h : ∀ (U : Y.Opens), IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U)) :
-- imply
  IsAffineHom f :=
-- proof
  (isAffineHom_iff f).mpr h

/--
[lemma27_finite_morphism_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec13AffineMorphisms.lean)
-/
@[path]
lemma lemma27_finite_morphism_iff
  {X Y : Scheme}
  {f : X ⟶ Y} :
-- imply
  IsFinite f ↔ IsAffineHom f ∧ ∀ (U : Y.Opens), IsAffineOpen U → (f.app U).hom.Finite :=
-- proof
  isFinite_iff f

/--
[lemma27_finite_is_affine](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec13AffineMorphisms.lean)
-/
@[path]
lemma lemma27_finite_is_affine
  {X Y : Scheme}
  {f : X ⟶ Y}
  [hf : IsFinite f] :
-- imply
  IsAffineHom f :=
-- proof
  ((isFinite_iff f).mp hf).1

/--
[lemma27_finite_ringHom_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec13AffineMorphisms.lean)
-/
@[path]
lemma lemma27_finite_ringHom_of_finite
  {X Y : Scheme}
  {f : X ⟶ Y}
  [hf : IsFinite f]
  {U : Y.Opens}
-- given
  (hU : IsAffineOpen U) :
-- imply
  (f.app U).hom.Finite :=
-- proof
  ((isFinite_iff f).mp hf).2 U hU

/--
[lemma27_finite_of_affine_and_finite_ringHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec13AffineMorphisms.lean)
-/
@[path]
lemma lemma27_finite_of_affine_and_finite_ringHom
  {X Y : Scheme}
  {f : X ⟶ Y}
-- given
  (hAff : IsAffineHom f)
  (hFin : ∀ (U : Y.Opens), IsAffineOpen U → (f.app U).hom.Finite) :
-- imply
  IsFinite f :=
-- proof
  (isFinite_iff f).mpr ⟨hAff, hFin⟩

/--
[lemma27_finite_specMap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec13AffineMorphisms.lean)
-/
@[path]
lemma lemma27_finite_specMap_iff
  {R S : CommRingCat}
  {f : R ⟶ S} :
-- imply
  IsFinite (Spec.map f) ↔ f.hom.Finite :=
-- proof
  IsFinite.SpecMap_iff f

/--
[lemma27_finite_iff_integral_and_finiteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec13AffineMorphisms.lean)
-/
@[path]
lemma lemma27_finite_iff_integral_and_finiteType
  {X Y : Scheme}
  {f : X ⟶ Y} :
-- imply
  IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f :=
-- proof
  IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f


-- created on 2026-10-23
