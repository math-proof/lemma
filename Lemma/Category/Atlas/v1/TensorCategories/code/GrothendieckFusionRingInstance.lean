import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.GrothendieckFusionRingInstance.Part2
open CategoryTheory MonoidalCategory Finset


/--
[jhFpDim_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckFusionRingInstance.lean)
-/
@[path]
private lemma jhFpDim_unit_eq
  [Field κ]
  {C : Type u}
  [Category.{v} C]
-- given
  (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData) :
-- imply
  jhFpDim fpd (𝟙_ C) = 1 := by
-- proof
  apply CategoryTheory.jhFpDim_unit fpd

/--
[jhFpDim_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckFusionRingInstance.lean)
-/
@[path]
private lemma jhFpDim_pos_eq
  [Field κ]
  {C : Type u}
  [Category.{v} C]
  {X : C}
-- given
  (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData) :
-- imply
  jhFpDim fpd X > 0 := by
-- proof
  apply CategoryTheory.jhFpDim_pos fpd X

/--
[jhFpDim_tensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckFusionRingInstance.lean)
-/
@[path]
private lemma jhFpDim_tensor_eq
  [Field κ]
  {C : Type u}
  [Category.{v} C]
  {X Y : C}
-- given
  (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData) :
-- imply
  jhFpDim fpd (X ⊗ Y) = jhFpDim fpd X * jhFpDim fpd Y := by
-- proof
  apply CategoryTheory.jhFpDim_tensor fpd X Y

/--
[jhFpDim_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckFusionRingInstance.lean)
-/
@[path]
private lemma jhFpDim_iso_eq
  [Field κ]
  {C : Type u}
  [Category.{v} C]
  {X Y : C}
-- given
  (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData)
  (h : Nonempty (X ≅ Y)) :
-- imply
  jhFpDim fpd X = jhFpDim fpd Y := by
-- proof
  apply CategoryTheory.jhFpDim_iso fpd X Y h


-- created on 2026-10-23
