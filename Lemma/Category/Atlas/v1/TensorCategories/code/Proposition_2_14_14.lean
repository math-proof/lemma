import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.DualCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.DualCategory
open CategoryTheory


/--
[CategoryTheory.proposition_2_14_14_basic_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_2_14_14.lean)
-/
@[path]
lemma CategoryTheory.proposition_2_14_14_basic_identity
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  [RigidCategory C]
  {inst_dual : LeftModuleCategory (DualCatObj C M) M}
  {X Y Z : M}
-- given
  (hExact : ExactModuleCategory C M) :
-- imply
  Nonempty ( @LeftModuleCategoryStruct.actObj C _ _ M _ _ (moduleIHom X Y) Z ≅ @LeftModuleCategoryStruct.actObj (DualCatObj C M) _ _ M _ inst_dual.toLeftModuleCategoryStruct (leftDualDualCat inst_dual (moduleIHomDual inst_dual Z X)) Y) :=
-- proof
  Proposition_2_14_14 hExact inst_dual X Y Z


-- created on 2026-10-23
