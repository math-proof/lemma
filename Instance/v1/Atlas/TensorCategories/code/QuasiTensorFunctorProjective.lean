/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctorProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Class.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w


namespace CategoryTheory

/-- In a rigid abelian monoidal category whose unit object is injective, every
projective object is injective. -/
noncomputable instance projectiveIsInjective_of_rigid
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Abelian C]
    [Injective (𝟙_ C)] :
    ProjectiveIsInjective C where
  injective_of_projective P _ := by
    exact Injective.mk (fun {A B : C} (f : A ⟶ P) (m : A ⟶ B) => by
      intro

      haveI : Mono (Pᘁ ◁ m) := by
        have adj := tensorLeftAdjunction (Pᘁ) ((Pᘁ)ᘁ)
        haveI := adj.rightAdjoint_preservesLimits
        haveI : (tensorLeft (Pᘁ)).PreservesMonomorphisms :=
          preservesMonomorphisms_of_preservesLimitsOfShape _
        exact (tensorLeft (Pᘁ)).map_mono m

      set f' : Pᘁ ⊗ A ⟶ 𝟙_ C :=
        (tensorLeftHomEquiv A P (Pᘁ) (𝟙_ C)).symm (f ≫ (ρ_ P).inv)

      obtain ⟨g', hg'⟩ := Injective.factors f' (Pᘁ ◁ m)

      refine ⟨(tensorLeftHomEquiv B P (Pᘁ) (𝟙_ C)) g' ≫ (ρ_ P).hom, ?_⟩
      rw [← cancel_mono (ρ_ P).inv]
      apply (tensorLeftHomEquiv A P (Pᘁ) (𝟙_ C)).symm.injective
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [tensorLeftHomEquiv_symm_naturality]
      simp only [Equiv.symm_apply_apply]
      exact hg')

/-- Any category satisfying `ProjectiveIsInjective` automatically satisfies the
mathlib `HasProjectiveImpliesInjective` typeclass. -/
noncomputable instance (priority := 100) hasProjectiveImpliesInjective_of_rigid
    (C : Type u) [Category.{v} C] [ProjectiveIsInjective C] :
    HasProjectiveImpliesInjective C where
  injective_of_projective P := ProjectiveIsInjective.injective_of_projective P inferInstance

/-- In a rigid abelian monoidal category whose unit object is projective, every
injective object is projective. -/
noncomputable instance injectiveIsProjective_of_rigid
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Abelian C]
    [Projective (𝟙_ C)] :
    ∀ (I : C), Injective I → Projective I := by
  intro I _
  exact Projective.mk (fun {A B : C} (f : I ⟶ B) (e : A ⟶ B) => by
    intro

    haveI : Epi (e ▷ (Iᘁ : C)) := by
      have adj := tensorRightAdjunction (Iᘁ : C) ((Iᘁ : C)ᘁ)
      haveI := adj.leftAdjoint_preservesColimits
      haveI : (tensorRight (Iᘁ : C)).PreservesEpimorphisms :=
        preservesEpimorphisms_of_preservesColimitsOfShape _
      exact (tensorRight (Iᘁ : C)).map_epi e

    set f' : 𝟙_ C ⟶ B ⊗ (Iᘁ : C) :=
      (tensorRightHomEquiv (𝟙_ C) I (Iᘁ : C) B) ((λ_ I).hom ≫ f)

    obtain ⟨g', hg'⟩ := Projective.factors f' (e ▷ (Iᘁ : C))

    refine ⟨(λ_ I).inv ≫ (tensorRightHomEquiv (𝟙_ C) I (Iᘁ : C) A).symm g', ?_⟩
    rw [Category.assoc, ← cancel_epi (λ_ I).hom,
        ← Category.assoc (λ_ I).hom, Iso.hom_inv_id, Category.id_comp]
    apply (tensorRightHomEquiv (𝟙_ C) I (Iᘁ : C) B).injective
    rw [tensorRightHomEquiv_naturality]
    simp only [Equiv.apply_symm_apply]
    exact hg')

/-- A rigid abelian monoidal category whose unit is both projective and injective
satisfies the quasi-Frobenius property: projectives coincide with injectives. -/
noncomputable instance quasiFrobeniusProperty_of_rigid
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Abelian C]
    [Injective (𝟙_ C)] [Projective (𝟙_ C)] :
    ExactModuleCategory.QuasiFrobeniusProperty C where
  projective_is_injective X _ :=
    (projectiveIsInjective_of_rigid C).injective_of_projective X inferInstance
  injective_is_projective X _ :=
    injectiveIsProjective_of_rigid C X inferInstance

end CategoryTheory
