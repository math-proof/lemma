import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.ModuleFunctorDefs
open Category MonoidalCategory LeftModCat


namespace CategoryTheory

/--
[Lemma_2_13_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_2_13_3.lean)
-/
@[path]
lemma Lemma_2_13_3
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M₁ : Type u₂}
  [Category.{v₂} M₁]
  [ExactModuleCategory C M₁]
  {M₂ : Type u₃}
  [Category.{v₃} M₂]
  [ExactModuleCategory C M₂]
  {F : ModuleFunctor C M₁ M₂} :
-- imply
  F.toFunctor.IsLeftAdjoint ∧ F.toFunctor.IsRightAdjoint :=
-- proof
  moduleFunctorHasAdjoints F

end CategoryTheory


-- created on 2026-10-23
