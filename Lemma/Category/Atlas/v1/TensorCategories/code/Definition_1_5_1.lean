import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.TensorCategories.code.Definition_1_5_1
open CategoryTheory MonoidalCategory TensorCategories


namespace TensorCategories

/--
[def_1_5_1_unit_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_5_1.lean)
-/
@[path]
lemma def_1_5_1_unit_compat
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {D : Type u₂}
  [Category.{v₂} D]
  [MonoidalCategory D]
  {F₁ F₂ : C ⥤ D}
  [F₁.LaxMonoidal]
  [F₂.LaxMonoidal]
  {η : F₁ ⟶ F₂}
  [NatTrans.IsMonoidal η] :
-- imply
  ε F₁ ≫ η.app (𝟙_ C) = ε F₂ :=
-- proof
  NatTrans.IsMonoidal.unit

end TensorCategories

namespace TensorCategories

/--
[def_1_5_1_tensor_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_5_1.lean)
-/
@[path]
lemma def_1_5_1_tensor_compat
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {D : Type u₂}
  [Category.{v₂} D]
  [MonoidalCategory D]
  {F₁ F₂ : C ⥤ D}
  [F₁.LaxMonoidal]
  [F₂.LaxMonoidal]
  {η : F₁ ⟶ F₂}
  [NatTrans.IsMonoidal η]
  {X Y : C} :
-- imply
  μ F₁ X Y ≫ η.app (X ⊗ Y) = (η.app X ⊗ₘ η.app Y) ≫ μ F₂ X Y :=
-- proof
  NatTrans.IsMonoidal.tensor X Y

end TensorCategories


-- created on 2026-10-23
