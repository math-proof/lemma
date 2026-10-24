import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.InternalHomEssSurjInstance
open CategoryTheory CategoryTheory.InternalHomEssSurjInst


/--
[rightMod_unit_act_eq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomEssSurjInstance.lean)
-/
@[path]
private lemma rightMod_unit_act_eq'_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
-- given
  (L : RightMod_ (A := 𝟙_ C)) :
-- imply
  L.mod.act = (ρ_ L.X).hom := by
-- proof
  apply CategoryTheory.InternalHomEssSurjInst.rightMod_unit_act_eq' C L


-- created on 2026-10-23
