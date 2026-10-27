import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.TensorCategories.code.UnitSemisimplicity.TensorExactness
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits TensorCategories


/--
[coevaluation_ne_zero_of_nonzero_obj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma coevaluation_ne_zero_of_nonzero_obj_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [RightRigidCategory C]
  [MonoidalPreadditive C]
  {X : C}
-- given
  (hX : ¬ IsZero X) :
-- imply
  η_ X Xᘁ ≠ 0 := by
-- proof
  apply TensorCategories.coevaluation_ne_zero_of_nonzero_obj X hX

/--
[isIso_of_epi_of_simple_src](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma isIso_of_epi_of_simple_src_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {X Y : C}
  [Simple X]
  {f : X ⟶ Y}
  [Epi f]
-- given
  (hf : f ≠ 0) :
-- imply
  IsIso f := by
-- proof
  apply TensorCategories.isIso_of_epi_of_simple_src f hf

/--
[rightAdjointMate_epi_of_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma rightAdjointMate_epi_of_mono_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [RightRigidCategory C]
  [LeftRigidCategory C]
  [MonoidalPreadditive C]
  {X : C}
  {f : X ⟶ 𝟙_ C}
  [Mono f] :
-- imply
  Epi (rightAdjointMate f) := by
-- proof
  apply TensorCategories.rightAdjointMate_epi_of_mono f

/--
[whiskerLeft_epi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma whiskerLeft_epi_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [LeftRigidCategory C]
  [MonoidalPreadditive C]
  {Y Z : C}
  {f : Y ⟶ Z}
  [Epi f]
  {W : C} :
-- imply
  Epi (W ◁ f) := by
-- proof
  apply TensorCategories.whiskerLeft_epi f W

/--
[whiskerLeft_rightAdjointMate_epi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma whiskerLeft_rightAdjointMate_epi_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [RightRigidCategory C]
  [LeftRigidCategory C]
  [MonoidalPreadditive C]
  {X : C}
  {f : X ⟶ 𝟙_ C}
  [Mono f] :
-- imply
  Epi (X ◁ rightAdjointMate f) := by
-- proof
  apply TensorCategories.whiskerLeft_rightAdjointMate_epi f

/--
[exists_epi_to_tensor_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma exists_epi_to_tensor_dual_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [RightRigidCategory C]
  [LeftRigidCategory C]
  [MonoidalPreadditive C]
  {X : C}
  [Simple X]
  {f : X ⟶ 𝟙_ C}
  [Mono f]
-- given
  (hf : f ≠ 0) :
-- imply
  ∃ (e : X ⟶ X ⊗ Xᘁ), Epi e ∧ e ≠ 0 := by
-- proof
  apply TensorCategories.exists_epi_to_tensor_dual f hf

/--
[simple_subobj_unit_retraction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma simple_subobj_unit_retraction_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [RightRigidCategory C]
  [LeftRigidCategory C]
  [MonoidalPreadditive C]
  {X : C}
  [Simple X]
  {f : X ⟶ 𝟙_ C}
  [Mono f]
-- given
  (hf : f ≠ 0) :
-- imply
  ∃ (g : 𝟙_ C ⟶ X), g ≠ 0 := by
-- proof
  apply TensorCategories.simple_subobj_unit_retraction f hf

/--
[exists_simple_subobject](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma exists_simple_subobject_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {X : C}
  [IsArtinianObject X]
-- given
  (hX : ¬ IsZero X) :
-- imply
  ∃ (S : C) (_ : Simple S) (i : S ⟶ X), Mono i ∧ i ≠ 0 := by
-- proof
  apply TensorCategories.exists_simple_subobject X hX

/--
[endUnit_isIso_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma endUnit_isIso_of_ne_zero_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  {f : 𝟙_ C ⟶ 𝟙_ C}
-- given
  (hEnd : ∀ (g : End (𝟙_ C)), g ≠ 0 → IsUnit g)
  (hf : f ≠ 0) :
-- imply
  IsIso f := by
-- proof
  apply TensorCategories.endUnit_isIso_of_ne_zero hEnd f hf

/--
[commSemisimpleRing_noNontrivialIdempotents_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma commSemisimpleRing_noNontrivialIdempotents_isUnit_eq
  {R : Type*}
  [CommRing R]
  [IsSemisimpleRing R]
-- given
  (htriv : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
-- imply
  ∀ g : R, g ≠ 0 → IsUnit g := by
-- proof
  apply TensorCategories.commSemisimpleRing_noNontrivialIdempotents_isUnit R htriv

/--
[endUnit_trivialIdempotents](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma endUnit_trivialIdempotents_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  {e : End (𝟙_ C)}
-- given
  (hIndecomp : Indecomposable (𝟙_ C))
  (he : IsIdempotentElem e) :
-- imply
  e = 0 ∨ e = 1 := by
-- proof
  apply TensorCategories.endUnit_trivialIdempotents hIndecomp e he

/--
[endUnit_isUnit_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma endUnit_isUnit_of_ne_zero_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [MonoidalBiexact C]
  [IsArtinianRing (End (𝟙_ C))]
  {g : End (𝟙_ C)}
-- given
  (hIndecomp : Indecomposable (𝟙_ C))
  (hg : g ≠ 0) :
-- imply
  IsUnit g := by
-- proof
  apply TensorCategories.endUnit_isUnit_of_ne_zero hIndecomp g hg

/--
[unitIsSimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean)
-/
@[path]
private lemma unitIsSimple_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [RightRigidCategory C]
  [LeftRigidCategory C]
  [MonoidalPreadditive C]
  [MonoidalBiexact C]
  [IsArtinianRing (End (𝟙_ C))]
  [IsArtinianObject (𝟙_ C)]
-- given
  (hIndecomp : Indecomposable (𝟙_ C)) :
-- imply
  Simple (𝟙_ C) where mono_isIso_iff_nonzero {Y} f := by
-- proof
  apply TensorCategories.unitIsSimple C hIndecomp


-- created on 2026-10-23
