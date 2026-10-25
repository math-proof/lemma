import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.TensorCategories.code.Bimodule
open CategoryTheory
open Category MonoidalCategory MonObj


namespace CategoryTheory

/--
[Bimodule.actions_commute](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Bimodule.lean)
-/
@[path]
lemma Bimodule.actions_commute
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {A B : Mon C}
  {M : Bimodule A B} :
-- imply
  M.actLeft ▷ B.X ≫ M.actRight = (α_ A.X M.X B.X).hom ≫ A.X ◁ M.actRight ≫ M.actLeft :=
-- proof
  M.middle_assoc

end CategoryTheory


-- created on 2026-10-23
