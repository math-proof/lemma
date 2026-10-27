import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
open CategoryTheory CategoryTheory.RightMod_


/--
[hom_ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategories.lean)
-/
@[path]
private lemma hom_ext_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {A : C}
  [MonObj A]
  {A}
  {M N : RightMod_ A}
  {f₁ f₂ : M ⟶ N}
-- given
  (h : f₁.hom = f₂.hom) :
-- imply
  f₁ = f₂ := by
-- proof
  apply CategoryTheory.RightMod_.hom_ext A f₁ f₂ h

/--
[id_hom'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategories.lean)
-/
@[path]
private lemma id_hom'_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {A : C}
  [MonObj A]
  {A}
  {M : RightMod_ A} :
-- imply
  (𝟙 M : M ⟶ M).hom = 𝟙 M.X := by
-- proof
  apply CategoryTheory.RightMod_.id_hom' A M

/--
[comp_hom'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategories.lean)
-/
@[path]
private lemma comp_hom'_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {A : C}
  [MonObj A]
  {A}
  {M N K : RightMod_ A}
  {f : M ⟶ N}
  {g : N ⟶ K} :
-- imply
  (f ≫ g).hom = f.hom ≫ g.hom := by
-- proof
  apply CategoryTheory.RightMod_.comp_hom' A f g


-- created on 2026-10-23
