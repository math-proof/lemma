import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec3Isomorphism
open CategoryTheory AlgebraicGeometry


namespace AlgebraicGeometry

/--
[isIsomorphism_iff_isIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Isomorphism.lean)
-/
@[path]
lemma isIsomorphism_iff_isIso
  {X Y : Scheme}
  {f : X ⟶ Y} :
-- imply
  IsIsomorphism f ↔ IsIso f := by
-- proof
  constructor
  · rintro ⟨g, hfg, hgf⟩
    exact ⟨⟨g, hfg, hgf⟩⟩
  · intro h
    exact ⟨inv f, IsIso.hom_inv_id f, IsIso.inv_hom_id f⟩

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[IsIsomorphism.inverse_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Isomorphism.lean)
-/
@[path]
lemma IsIsomorphism.inverse_unique
  {X Y : Scheme}
  {f : X ⟶ Y}
  {g₁ g₂ : Y ⟶ X}
-- given
  (_hf : IsIsomorphism f)
  (hg₁ : f ≫ g₁ = 𝟙 X ∧ g₁ ≫ f = 𝟙 Y)
  (hg₂ : f ≫ g₂ = 𝟙 X ∧ g₂ ≫ f = 𝟙 Y) :
-- imply
  g₁ = g₂ := by
-- proof
  calc g₁ = 𝟙 Y ≫ g₁ := by simp
    _ = (g₂ ≫ f) ≫ g₁ := by rw [hg₂.2]
    _ = g₂ ≫ (f ≫ g₁) := by rw [Category.assoc]
    _ = g₂ ≫ 𝟙 X := by rw [hg₁.1]
    _ = g₂ := by simp

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[isIsomorphism_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Isomorphism.lean)
-/
@[path]
lemma isIsomorphism_id
  {X : Scheme} :
-- imply
  IsIsomorphism (𝟙 X) :=
-- proof
  ⟨𝟙 X, Category.comp_id _, Category.comp_id _⟩

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[IsIsomorphism.comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Isomorphism.lean)
-/
@[path]
lemma IsIsomorphism.comp
  {X Y Z : Scheme}
  {f : X ⟶ Y}
  {g : Y ⟶ Z}
-- given
  (hf : IsIsomorphism f)
  (hg : IsIsomorphism g) :
-- imply
  IsIsomorphism (f ≫ g) := by
-- proof
  obtain ⟨f', hff', hf'f⟩ := hf
  obtain ⟨g', hgg', hg'g⟩ := hg
  refine ⟨g' ≫ f', ?_, ?_⟩
  · calc (f ≫ g) ≫ (g' ≫ f')
    = f ≫ (g ≫ g') ≫ f' := by simp [Category.assoc]
    _ = f ≫ 𝟙 Y ≫ f' := by rw [hgg']
    _ = f ≫ f' := by simp
    _ = 𝟙 X := hff'
  · calc (g' ≫ f') ≫ (f ≫ g)
    = g' ≫ (f' ≫ f) ≫ g := by simp [Category.assoc]
    _ = g' ≫ 𝟙 Y ≫ g := by rw [hf'f]
    _ = g' ≫ g := by simp
    _ = 𝟙 Z := hg'g

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[IsIsomorphism.inverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Isomorphism.lean)
-/
@[path]
lemma IsIsomorphism.inverse
  {X Y : Scheme}
  {f : X ⟶ Y}
-- given
  (hf : IsIsomorphism f) :
-- imply
  ∃ g : Y ⟶ X, IsIsomorphism g := by
-- proof
  obtain ⟨g, hfg, hgf⟩ := hf
  exact ⟨g, f, hgf, hfg⟩

end AlgebraicGeometry


-- created on 2026-10-23
