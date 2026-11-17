module

public import Mathlib
public import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory

public section

open Category MonoidalCategory LeftModCat Limits


namespace CategoryTheory

/--
[Lemma_2_7_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleProjectives.lean)
-/
public theorem Lemma_2_7_1
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [EnoughProjectives C]
-- given
  (hEpi : ∀ {X Y : C} (f : X ⟶ Y) (N : M), Epi f → Epi (f ▷ᵐ N)) :
-- imply
  EnoughProjectives M :=
-- proof
  ExactModuleCategory.enoughProjectives_of_exact hEpi

end CategoryTheory


-- created on 2026-10-23
