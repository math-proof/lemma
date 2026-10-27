import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.AdjustedResolutions.Part2
open CategoryTheory Category Limits AdjustedResolutions


namespace AdjustedResolutions

/--
[injective_isAdjustedToFunctor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjustedResolutions.lean)
-/
@[path]
lemma injective_isAdjustedToFunctor
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [HasInjectiveResolutions C]
  [Category D]
  [Abelian D]
  {F : C ⥤ D}
  [F.Additive]
  {M : C}
  [Injective M] :
-- imply
  IsAdjustedToFunctor F M := by
-- proof
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact Functor.isZero_rightDerived_obj_injective_succ F k M

end AdjustedResolutions

namespace AdjustedResolutions

/--
[injRes_objects_adjusted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjustedResolutions.lean)
-/
@[path]
lemma injRes_objects_adjusted
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [HasInjectiveResolutions C]
  [Category D]
  [Abelian D]
  {F : C ⥤ D}
  [F.Additive]
  {M : C}
  {I : InjectiveResolution M}
  {n : ℕ} :
-- imply
  IsAdjustedToFunctor F (I.cocomplex.X n) :=
-- proof
  injective_isAdjustedToFunctor F (I.cocomplex.X n)

end AdjustedResolutions


-- created on 2026-10-23
