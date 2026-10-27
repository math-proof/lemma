import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.Definition_2_9_24
open CategoryTheory
open Category MonoidalCategory


namespace CategoryTheory

/--
[Definition_2_9_24_Bimodule.actions_commute](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_9_24.lean)
-/
@[path]
lemma Definition_2_9_24_Bimodule.actions_commute
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {A B : Mon C}
  {M : Definition_2_9_24_Bimodule A B} :
-- imply
  M.actLeft ▷ B.X ≫ M.actRight = (α_ A.X M.X B.X).hom ≫ A.X ◁ M.actRight ≫ M.actLeft :=
-- proof
  M.middle_assoc

end CategoryTheory


-- created on 2026-10-23
