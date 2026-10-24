import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitSemisimplicity.UnitSimple
import Lemma.Category.Atlas.v1.TensorCategories.code.UnitSemisimplicity.UnitSimple
open CategoryTheory MonoidalCategory Limits


/--
[Theorem_1_15_8_unit_is_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_15_8.lean)
-/
@[path]
lemma Theorem_1_15_8_unit_is_simple
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [RightRigidCategory C]
  [LeftRigidCategory C]
  [MonoidalPreadditive C]
  [TensorCategories.MonoidalBiexact C]
  [IsArtinianRing (End (𝟙_ C))]
  [IsArtinianObject (𝟙_ C)]
-- given
  (hIndecomp : Indecomposable (𝟙_ C)) :
-- imply
  Simple (𝟙_ C) :=
-- proof
  TensorCategories.unitIsSimple C hIndecomp


-- created on 2026-10-23
