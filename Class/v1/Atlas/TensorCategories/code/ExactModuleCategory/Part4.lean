module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Instance.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part3
public section
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- `ActionRightExact` asserts that whiskering by a projective `Q ∈ C` on the left of
the module action preserves short exact sequences. -/
class ActionRightExact
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M] where
  actWhiskerLeft_comp_cokernel_zero :
    ∀ (Q : C) [Projective Q] {A B : M} (e : A ⟶ B) [Mono e],
      Q ◁ᵐ e ≫ Q ◁ᵐ (cokernel.π e) = 0
  actWhiskerLeft_shortExact :
    ∀ (Q : C) [Projective Q] {A B : M} (e : A ⟶ B) [Mono e],
      (ShortComplex.mk (Q ◁ᵐ e) (Q ◁ᵐ (cokernel.π e))
        (actWhiskerLeft_comp_cokernel_zero Q e)).ShortExact

end ExactModuleCategory
end CategoryTheory
