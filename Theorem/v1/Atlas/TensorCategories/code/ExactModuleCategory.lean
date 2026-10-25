/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Noetherian
import Mathlib.RingTheory.Finiteness.Defs
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- In a rigid monoidal category, the left dual of a projective object is projective. -/
theorem leftDualOfProjectiveIsProjective
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
    (P : C) [Projective P] :
    Projective (HasLeftDual.leftDual P) where
  factors {E X} f e _ := by
    let Φ := tensorRightHomEquiv (𝟙_ C) (ᘁP) P
    let f₁ : 𝟙_ C ⊗ HasLeftDual.leftDual P ⟶ X := (λ_ _).hom ≫ f
    let f₂ : 𝟙_ C ⟶ X ⊗ P := Φ X f₁

    have adj : tensorRight P ⊣ tensorRight (Pᘁ) := tensorRightAdjunction P (Pᘁ)
    have : PreservesColimitsOfSize.{0, 0} (tensorRight P) :=
      adj.leftAdjoint_preservesColimits
    have : (tensorRight P).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _

    have : Epi (e ▷ P) := (tensorRight P).map_epi e

    haveI : Projective (X ⊗ P) := by
      have adj1 : tensorLeft X ⊣ tensorLeft (ᘁX) := tensorLeftAdjunction (ᘁX) X
      have adj2 : tensorLeft (ᘁX) ⊣ tensorLeft (ᘁ(ᘁX)) := tensorLeftAdjunction (ᘁ(ᘁX)) (ᘁX)
      haveI : PreservesColimitsOfSize.{0, 0} (tensorLeft (ᘁX)) :=
        adj2.leftAdjoint_preservesColimits
      haveI : (tensorLeft (ᘁX)).PreservesEpimorphisms :=
        preservesEpimorphisms_of_preservesColimitsOfShape _
      exact adj1.map_projective P ‹_›

    obtain ⟨s, hs⟩ := Projective.factors (𝟙 (X ⊗ P)) (e ▷ P)


    let g₂ : 𝟙_ C ⟶ E ⊗ P := f₂ ≫ s

    let g₁ : 𝟙_ C ⊗ HasLeftDual.leftDual P ⟶ E := (Φ E).symm g₂

    use (λ_ _).inv ≫ g₁


    have key : g₁ ≫ e = f₁ := by
      apply (Φ X).injective
      rw [tensorRightHomEquiv_naturality g₁ e]
      change (Φ E) g₁ ≫ e ▷ P = (Φ X) f₁
      simp only [g₁, g₂, Equiv.apply_symm_apply]
      simp only [f₂, assoc, hs, comp_id]
    simp only [assoc, key, f₁, Iso.inv_hom_id_assoc]

end ExactModuleCategory
end CategoryTheory
