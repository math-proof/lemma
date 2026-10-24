import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_45_2
open CategoryTheory MonoidalCategory


/--
[Proposition_1_45_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_45_2.lean)
-/
@[path]
lemma Proposition_1_45_2
  [Field κ]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear κ C]
  [Abelian C]
  [MonoidalCategory C]
  [MonoidalPreadditive C]
  [MonoidalLinear κ C]
  [RigidCategory C]
  [cfd : CategoricalFusionData κ C] :
-- imply
  (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).IsTransitive :=
-- proof
  CategoricalFusionData.toFusionRing.isTransitive


-- created on 2026-10-23
