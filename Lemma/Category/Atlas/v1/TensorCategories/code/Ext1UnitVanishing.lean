import Mathlib
import sympy.Basic
import Class.v1.Atlas.TensorCategories.code.Ext1UnitVanishing.Part2
open CategoryTheory MonoidalCategory Category Limits TensorCategories


namespace TensorCategories

/--
[Ext1Vanishes.exists_section](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean)
-/
@[path]
lemma Ext1Vanishes.exists_section
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {X Y : C}
  {V : C}
  {f : Y ⟶ V}
  {g : V ⟶ X}
  {hfg : f ≫ g = 0}
-- given
  (h : Ext1Vanishes X Y)
  (hse : (ShortComplex.mk f g hfg).ShortExact) :
-- imply
  ∃ s : X ⟶ V, s ≫ g = 𝟙 X := by
-- proof
  obtain ⟨spl⟩ := h V f g hfg hse
  exact ⟨spl.s, spl.s_g⟩

end TensorCategories

namespace TensorCategories

/--
[Ext1Vanishes.exists_retraction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean)
-/
@[path]
lemma Ext1Vanishes.exists_retraction
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {X Y : C}
  {V : C}
  {f : Y ⟶ V}
  {g : V ⟶ X}
  {hfg : f ≫ g = 0}
-- given
  (h : Ext1Vanishes X Y)
  (hse : (ShortComplex.mk f g hfg).ShortExact) :
-- imply
  ∃ r : V ⟶ Y, f ≫ r = 𝟙 Y := by
-- proof
  obtain ⟨spl⟩ := h V f g hfg hse
  exact ⟨spl.r, spl.f_r⟩

end TensorCategories

namespace TensorCategories

/--
[Ext1Vanishes.full_splitting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean)
-/
@[path]
lemma Ext1Vanishes.full_splitting
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {X Y : C}
  {V : C}
  {f : Y ⟶ V}
  {g : V ⟶ X}
  {hfg : f ≫ g = 0}
-- given
  (h : Ext1Vanishes X Y)
  (hse : (ShortComplex.mk f g hfg).ShortExact) :
-- imply
  ∃ (r : V ⟶ Y) (s : X ⟶ V), f ≫ r = 𝟙 Y ∧ s ≫ g = 𝟙 X ∧ r ≫ f + g ≫ s = 𝟙 V := by
-- proof
  obtain ⟨spl⟩ := h V f g hfg hse
  exact ⟨spl.r, spl.s, spl.f_r, spl.s_g, spl.id⟩

end TensorCategories

namespace TensorCategories

/--
[Ext1Vanishes.splitting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean)
-/
@[path]
lemma Ext1Vanishes.splitting
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {X Y : C}
  {S : ShortComplex C}
-- given
  (h : Ext1Vanishes X Y)
  (hse : S.ShortExact)
  (hX : S.X₃ = X)
  (hY : S.X₁ = Y) :
-- imply
  Nonempty S.Splitting := by
-- proof
  subst hX; subst hY
  exact h S.X₂ S.f S.g S.zero hse

end TensorCategories

namespace TensorCategories

/--
[FiniteRingCategory.enough_projectives](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean)
-/
@[path]
lemma FiniteRingCategory.enough_projectives
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [FiniteRingCategory k C] :
-- imply
  EnoughProjectives C :=
-- proof
  FiniteRingCategory.enoughProj k

end TensorCategories

namespace TensorCategories

/--
[FiniteRingCategory.hom_finite_dimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean)
-/
@[path]
lemma FiniteRingCategory.hom_finite_dimensional
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [FiniteRingCategory k C]
  {X Y : C} :
-- imply
  FiniteDimensional k (X ⟶ Y) :=
-- proof
  FiniteRingCategory.homFiniteDim X Y

end TensorCategories

namespace TensorCategories

/--
[ext1Vanishes_unit_unit_of_charZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean)
-/
@[path]
lemma ext1Vanishes_unit_unit_of_charZero
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {k : Type w}
  [Field k]
  [CharZero k]
  {C : Type u}
  [Category.{v} C]
  [FiniteRingCategory k C]
  [Simple (𝟙_ C)]
  [HasDerivationFromExtension k C]
  [HasHigherDerivationContradiction k] :
-- imply
  Ext1Vanishes (𝟙_ C) (𝟙_ C) := by
-- proof
  intro V f g hfg hse
  by_contra h_not_split
  obtain ⟨A, instR, instA, instFD, ε, hds, hne⟩ :=
    HasDerivationFromExtension.higher_derivation_from_nonsplit_ext (k := k) V f g hfg hse
      (fun ⟨s⟩ => h_not_split ⟨s⟩)
  exact hne (@HasHigherDerivationContradiction.higher_derivation_vanishes
    k _ _ _ A instR instA instFD ε hds)

end TensorCategories


-- created on 2026-10-23
