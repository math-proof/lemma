import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ConservativeFunctor
open CategoryTheory


/--
[jointlyReflectIsomorphisms_of_conservative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConservativeFunctor.lean)
-/
@[path]
lemma jointlyReflectIsomorphisms_of_conservative
  {C : Type u₁}
  [Category.{v₁} C]
  {D : Type u₂}
  [Category.{v₂} D]
  {R : C ⥤ D}
  [R.ReflectsIsomorphisms] :
-- imply
  JointlyReflectIsomorphisms (fun (_ : PUnit.{1}) => R) where isIso f h := by
-- proof
  haveI := h PUnit.unit
  exact isIso_of_reflects_iso f R

/--
[conservative_exact_functor_reflects_exact_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConservativeFunctor.lean)
-/
@[path]
lemma conservative_exact_functor_reflects_exact_iff
  {C : Type u₁}
  [Category.{v₁} C]
  {D : Type u₂}
  [Category.{v₂} D]
  [Abelian C]
  [Abelian D]
  {R : C ⥤ D}
  [R.PreservesZeroMorphisms]
  [R.PreservesHomology]
  [R.ReflectsIsomorphisms]
  {S : ShortComplex C} :
-- imply
  S.Exact ↔ (S.map R).Exact := by
-- proof
  have hJ := jointlyReflectIsomorphisms_of_conservative R
  rw [hJ.exact_iff (I := PUnit.{1}) S]
  exact ⟨fun h => h PUnit.unit, fun h _ => h⟩


-- created on 2026-10-23
