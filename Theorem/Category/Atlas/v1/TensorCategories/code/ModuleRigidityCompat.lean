module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.v1.Atlas.TensorCategories.code.ModuleRigidityCompat

@[expose] public section

open CategoryTheory CategoryTheory.ExactModuleCategory


/--
[actWhiskerLeft_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleRigidityCompat.lean)
-/
@[path]
private theorem actWhiskerLeft_comp_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [LeftRigidCategory C]
  {X : C}
  {N₁ N₂ N₃ : M}
  {f : N₁ ⟶ N₂}
  {g : N₂ ⟶ N₃} :
-- imply
  X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g := by
-- proof
  apply CategoryTheory.ExactModuleCategory.actWhiskerLeft_comp X f g


-- created on 2026-10-23
