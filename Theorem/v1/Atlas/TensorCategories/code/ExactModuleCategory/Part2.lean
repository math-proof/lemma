module

public import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
public import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Noetherian
public import Mathlib.RingTheory.Finiteness.Defs
public import Class.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part5
public section
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- Convenience accessor: under `BiexactAction`, left whiskering by `L` preserves monos. -/
public theorem actWhiskerLeft_preserves_mono
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]
    [BiexactAction C M]
    (L : C) {A B : M} (f : A ⟶ B) [Mono f] :
    Mono (L ◁ᵐ f) :=
  BiexactAction.actWhiskerLeft_preserves_mono L f

/-- Convenience accessor: under `BiexactAction`, left whiskering by `L` preserves epis. -/
public theorem actWhiskerLeft_preserves_epi
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]
    [BiexactAction C M]
    (L : C) {A B : M} (f : A ⟶ B) [Epi f] :
    Epi (L ◁ᵐ f) :=
  BiexactAction.actWhiskerLeft_preserves_epi L f

end ExactModuleCategory
end CategoryTheory
