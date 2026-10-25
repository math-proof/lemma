/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HomExactImpliesExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.ModuleFunctorDefs
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

/-- The module category `M` is nonzero: it contains some object that is not initial. -/
class NonzeroModuleCategory (M : Type u₂) [Category.{v₂} M] : Prop where
  exists_nonzero : ∃ (X : M), IsEmpty (IsInitial X)

end CategoryTheory
