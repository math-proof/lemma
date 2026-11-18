/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Class.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4

@[expose] public section

set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- If `Q` is projective and `e : A ⟶ B` is a mono in the module category, then
`Q ◁ e` is a split monomorphism. -/
noncomputable def action_projective_split_mono
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [Abelian M] [ActionRightExact C M]
    (Q : C) [Projective Q] {A B : M} (e : A ⟶ B) [Mono e] :
    SplitMono (Q ◁ᵐ e) := by

  let S := ShortComplex.mk (Q ◁ᵐ e) (Q ◁ᵐ (cokernel.π e))
    (ActionRightExact.actWhiskerLeft_comp_cokernel_zero Q e)

  have hSE : S.ShortExact := ActionRightExact.actWhiskerLeft_shortExact Q e

  haveI : Projective S.X₃ := action_preserves_projective Q (cokernel e)

  exact hSE.splittingOfProjective.splitMono_f

/-- Specialization of `action_projective_split_mono` to the left dual `*P` of a
projective `P` in a rigid category. -/
noncomputable def action_dual_split_mono
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [Abelian M] [ActionRightExact C M]
    (P : C) [Projective P] {A B : M} (e : A ⟶ B) [Mono e] :
    SplitMono ((ᘁP) ◁ᵐ e) :=
  action_projective_split_mono (ᘁP) e

/-- Corollary 2.7.4 (EGNO), second half: In an exact module category over a rigid
multitensor category, every injective object is projective. -/
def IsModSubquotient {A : Type*} [Category A] (Y X : A) : Prop :=
  ∃ (Z : A) (i : Z ⟶ X) (p : Z ⟶ Y), Mono i ∧ Epi p

end ExactModuleCategory
end CategoryTheory
