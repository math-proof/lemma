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
import Instance.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part2
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- Compatibility class providing the adjunction between `P ⊗ -` and `(*P) ⊗ -` on the
module category side of a rigid monoidal action, together with naturality. -/
class ModuleRigidityCompat
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
    (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M] where
  modRigidForward : ∀ (P : C) (N A : M), (A ⟶ P ⊗ᵐ N) → ((ᘁP) ⊗ᵐ A ⟶ N)
  modRigidBackward : ∀ (P : C) (N A : M), ((ᘁP) ⊗ᵐ A ⟶ N) → (A ⟶ P ⊗ᵐ N)
  modRigid_left_inv : ∀ (P : C) (N A : M) (g : (ᘁP) ⊗ᵐ A ⟶ N),
    modRigidForward P N A (modRigidBackward P N A g) = g
  modRigid_right_inv : ∀ (P : C) (N A : M) (f : A ⟶ P ⊗ᵐ N),
    modRigidBackward P N A (modRigidForward P N A f) = f
  modRigidForward_natural : ∀ (P : C) (N : M) {A B : M} (e : A ⟶ B) (g : B ⟶ P ⊗ᵐ N),
    modRigidForward P N A (e ≫ g) = ((ᘁP) ◁ᵐ e) ≫ modRigidForward P N B g

end ExactModuleCategory
end CategoryTheory
