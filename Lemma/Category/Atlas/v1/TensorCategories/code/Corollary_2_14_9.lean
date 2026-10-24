import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.Corollary_2_14_9
open CategoryTheory
open Category MonoidalCategory ModFun Limits


namespace CategoryTheory

/--
[corollary_2_14_9](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_2_14_9.lean)
-/
@[path]
lemma corollary_2_14_9
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [RigidCategory C]
  [EnoughProjectives C]
  [HasZeroMorphisms C]
  {M : Type u₂}
  [Category.{v₂} M]
  [LeftModuleCategory' C M]
  [UnivLE.{u₂, v₂}]
-- given
  (h_simple : Simple (𝟙_ C))
  (hM : IsExactModuleCategory' C M) :
-- imply
  letI catD := DualCatObj'.categoryInstance C M letI monD := DualCatObj'.monoidalCategoryInstance C M letI modD := DualCatObj'.evalModuleInstance C M @IsIndecomposableModuleCategory' (DualCatObj' C M) catD monD M _ modD := by
-- proof
  letI catD := DualCatObj'.categoryInstance C M
  letI monD := DualCatObj'.monoidalCategoryInstance C M
  letI modD := DualCatObj'.evalModuleInstance C M
  exact ⟨nonzeroModCat_of_exact' h_simple hM,
    thm_2_14_6_lem_2_14_3_indecomposable' h_simple hM⟩

end CategoryTheory


-- created on 2026-10-23
