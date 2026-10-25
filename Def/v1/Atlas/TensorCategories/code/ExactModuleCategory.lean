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
import Class.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part3
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- The hom-set adjunction `(A ⟶ P ⊗ N) ≃ ((*P) ⊗ A ⟶ N)` extracted from the
`ModuleRigidityCompat` data. -/
def modHomTensorAdj
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [ModuleRigidityCompat C M]
    (P : C) (N A : M) : (A ⟶ P ⊗ᵐ N) ≃ ((ᘁP) ⊗ᵐ A ⟶ N) where
  toFun := ModuleRigidityCompat.modRigidForward P N A
  invFun := ModuleRigidityCompat.modRigidBackward P N A
  left_inv := ModuleRigidityCompat.modRigid_right_inv P N A
  right_inv := ModuleRigidityCompat.modRigid_left_inv P N A

end ExactModuleCategory
end CategoryTheory
