import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SheafDef
open TopCat TopCat.Presheaf CategoryTheory CategoryTheory.Limits
open TopCat TopCat.Presheaf CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite


namespace TopCat.Presheaf

/--
[isSheafUniqueGluing_iff_gluing_and_locality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafDef.lean)
-/
@[path]
lemma isSheafUniqueGluing_iff_gluing_and_locality
  [Category C]
  {FC : C → C → Type*}
  {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC]
  {X : TopCat.{x}}
  {F : Presheaf C X} :
-- imply
  F.IsSheafUniqueGluing ↔ F.SatisfiesGluing ∧ F.SatisfiesLocality := by
-- proof
  constructor
  · intro h
    refine ⟨fun ι U sf hcompat => ?_, fun ι U s t heq => ?_⟩
    ·
      obtain ⟨s, hs, _⟩ := h U sf hcompat
      exact ⟨s, hs⟩
    ·
      let sf := fun i => F.map (Opens.leSupr U i).op s
      have hcompat_sf : F.IsCompatible U sf := by
        intro i j
        simp only [sf, ← ConcreteCategory.comp_apply, ← F.map_comp]
        rfl
      obtain ⟨gl, _, huniq⟩ := h U sf hcompat_sf
      have hs : F.IsGluing U sf s := fun i => rfl
      have ht : F.IsGluing U sf t := by
        intro i; simp only [sf]; exact (heq i).symm
      exact (huniq s hs).trans (huniq t ht).symm
  ·
    intro ⟨hglue, hloc⟩ ι U sf hcompat
    obtain ⟨s, hs⟩ := hglue U sf hcompat
    exact ⟨s, hs, fun t ht => hloc U t s (fun i => by rw [ht i, hs i])⟩
section ConcreteComplete
variable [HasLimitsOfSize.{x, x} C] [(forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{x, x} (forget C)]

end TopCat.Presheaf

namespace TopCat.Presheaf

/--
[isSheaf_iff_gluing_and_locality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafDef.lean)
-/
@[path]
lemma isSheaf_iff_gluing_and_locality
  [Category C]
  {FC : C → C → Type*}
  {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC]
  {X : TopCat.{x}}
  {F : Presheaf C X}
  [HasLimitsOfSize.{x, x} C]
  [(forget C).ReflectsIsomorphisms] :
-- imply
  F.IsSheaf ↔ F.SatisfiesGluing ∧ F.SatisfiesLocality := by
-- proof
  rw [isSheaf_iff_isSheafUniqueGluing, isSheafUniqueGluing_iff_gluing_and_locality]

end TopCat.Presheaf

namespace TopCat.Presheaf

/--
[_root_.TopCat.Sheaf.satisfiesGluing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafDef.lean)
-/
@[path]
lemma _root_.TopCat.Sheaf.satisfiesGluing
  [Category C]
  {FC : C → C → Type*}
  {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC]
  {X : TopCat.{x}}
  {F : Presheaf C X}
  [HasLimitsOfSize.{x, x} C]
  [(forget C).ReflectsIsomorphisms]
  {ℱ : TopCat.Sheaf C X} :
-- imply
  SatisfiesGluing ℱ.1 :=
-- proof
  ((isSheaf_iff_gluing_and_locality ℱ.1).mp ℱ.2).1

end TopCat.Presheaf

namespace TopCat.Presheaf

/--
[_root_.TopCat.Sheaf.satisfiesLocality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafDef.lean)
-/
@[path]
lemma _root_.TopCat.Sheaf.satisfiesLocality
  [Category C]
  {FC : C → C → Type*}
  {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC]
  {X : TopCat.{x}}
  {F : Presheaf C X}
  [HasLimitsOfSize.{x, x} C]
  [(forget C).ReflectsIsomorphisms]
  {ℱ : TopCat.Sheaf C X} :
-- imply
  SatisfiesLocality ℱ.1 :=
-- proof
  ((isSheaf_iff_gluing_and_locality ℱ.1).mp ℱ.2).2

end TopCat.Presheaf


-- created on 2026-10-23
