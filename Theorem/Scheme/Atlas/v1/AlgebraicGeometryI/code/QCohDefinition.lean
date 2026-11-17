module

public import Mathlib
public import Def.v1.Atlas.AlgebraicGeometryI.code.QCohDefinition

public section

open CategoryTheory


/--
[isConservative_iff_reflectsIsomorphisms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohDefinition.lean)
-/
public theorem isConservative_iff_reflectsIsomorphisms
  {C : Type u₁}
  [Category.{v₁} C]
  {D : Type u₂}
  [Category.{v₂} D]
  {F : C ⥤ D} :
-- imply
  IsConservative F ↔ F.ReflectsIsomorphisms where mp h :=
-- proof
  ⟨fun f => h f ‹_›⟩
    mpr := fun ⟨inst⟩ _ _ g hiso => @inst _ _ g hiso


-- created on 2026-10-23
