/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_2_10_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂

/-- Corollary 2.10.5 (1): For a fixed M₁ in a module category M over C, the assignment
M₂ ↦ Hom(M₁, M₂) defines a module functor M → C, where Hom denotes the internal Hom. -/


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
variable (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
variable [HasModuleInternalHom C M]

end CategoryTheory
