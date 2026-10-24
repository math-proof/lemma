import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.PullbackPresheafDef
open CategoryTheory TopologicalSpace Opposite TopCat TopCat.Presheaf


namespace TopCat.Presheaf

/--
[pullbackPresheaf_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PullbackPresheafDef.lean)
-/
@[path]
lemma pullbackPresheaf_eq
  {C : Type u}
  [Category.{v} C]
  [Limits.HasColimits C]
  {X Y : TopCat.{v}}
  {f : X ⟶ Y}
  {𝒢 : Y.Presheaf C} :
-- imply
  pullbackPresheaf C f 𝒢 = (pullback C f).obj 𝒢 :=
-- proof
  rfl

end TopCat.Presheaf


-- created on 2026-10-23
