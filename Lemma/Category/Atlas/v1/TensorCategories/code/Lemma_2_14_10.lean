import Mathlib
import sympy.Basic
import Class.v1.Atlas.TensorCategories.code.DualCatDefs
open Category MonoidalCategory ModFun


namespace CategoryTheory

/--
[Lemma_2_14_10](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_2_14_10.lean)
-/
@[path]
lemma Lemma_2_14_10
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [RigidCategory C]
  [EnoughProjectives C]
  {M : Type u₂}
  [Category.{v₂} M]
  [LeftModuleCategory' C M]
  [UnivLE.{u₂, v₂}]
  {M₁ : Type u₂}
  [Category.{v₂} M₁]
  [LeftModuleCategory' C M₁]
-- given
  (hM : IsExactModuleCategory' C M) :
-- imply
  letI catD := DualCatObj'.categoryInstance C M letI _monD := DualCatObj'.monoidalCategoryInstance C M letI catF := ModuleFunctor'.categoryInstance C M₁ M letI modF := ModuleFunctor'.leftModuleInstance C M₁ M ∀ (P : DualCatObj' C M) (F : ModuleFunctor' C M₁ M), @Projective (DualCatObj' C M) catD P → @Projective (ModuleFunctor' C M₁ M) catF (modF.actObj P F) :=
-- proof
  funC_exact_over_dualCat hM M₁

end CategoryTheory

namespace CategoryTheory

/--
[lemma_2_14_10](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_2_14_10.lean)
-/
@[path]
lemma lemma_2_14_10
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [RigidCategory C]
  [EnoughProjectives C]
  {M : Type u₂}
  [Category.{v₂} M]
  [LeftModuleCategory' C M]
  [UnivLE.{u₂, v₂}]
  {M₁ : Type u₂}
  [Category.{v₂} M₁]
  [LeftModuleCategory' C M₁]
-- given
  (hM : IsExactModuleCategory' C M) :
-- imply
  letI catD := DualCatObj'.categoryInstance C M letI _monD := DualCatObj'.monoidalCategoryInstance C M letI catF := ModuleFunctor'.categoryInstance C M₁ M letI modF := ModuleFunctor'.leftModuleInstance C M₁ M ∀ (P : DualCatObj' C M) (F : ModuleFunctor' C M₁ M), @Projective (DualCatObj' C M) catD P → @Projective (ModuleFunctor' C M₁ M) catF (modF.actObj P F) :=
-- proof
  funC_exact_over_dualCat hM M₁

end CategoryTheory


-- created on 2026-10-23
