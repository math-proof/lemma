import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1.Part3
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry


/--
[pushforward_sheaf_of_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10SheavesP1.lean)
-/
@[path]
lemma pushforward_sheaf_of_sheaf
  {C : Type u}
  [Category.{v} C]
  {X Y : TopCat.{w}}
  {f : X ⟶ Y}
  {F : TopCat.Presheaf C X}
-- given
  (h : F.IsSheaf) :
-- imply
  ((TopCat.Presheaf.pushforward C f).obj F).IsSheaf :=
-- proof
  TopCat.Sheaf.pushforward_sheaf_of_sheaf f h

/--
[sheafification_iso_of_isSheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10SheavesP1.lean)
-/
@[path]
lemma sheafification_iso_of_isSheaf
  {C : Type u}
  [Category.{v} C]
  {J : GrothendieckTopology C}
  [Category D]
  [HasWeakSheafify J D]
  {P : Cᵒᵖ ⥤ D}
-- given
  (hP : Presheaf.IsSheaf J P) :
-- imply
  IsIso (toSheafify J P) :=
-- proof
  isIso_toSheafify J hP

/--
[stalk_functor_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10SheavesP1.lean)
-/
@[path]
lemma stalk_functor_exact
  {C : Type v}
  [Category.{u} C]
  [HasColimits C]
  [HasLimits C]
  {FC : C → C → Type*}
  {CC : C → Type u}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC]
  [PreservesFilteredColimits (CategoryTheory.forget C)]
  [PreservesLimits (CategoryTheory.forget C)]
  [Abelian C]
  {X : TopCat.{u}}
  {S : ShortComplex (TopCat.Sheaf C X)} :
-- imply
  S.Exact ↔ ∀ x : X, (S.map (TopCat.Sheaf.forget C X ⋙ TopCat.Presheaf.stalkFunctor C x)).Exact :=
-- proof
  TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S


-- created on 2026-10-23
