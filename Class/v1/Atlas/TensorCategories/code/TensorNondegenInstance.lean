/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegenInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.TensorNondegen.ZeroTensorZero
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorNondegen.ZeroTensorZero
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorNondegen.DualZero
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorNondegen.EvalCoevalArg
import Theorem.v1.Atlas.TensorCategories.code.TensorNondegen.DualZero
import Theorem.v1.Atlas.TensorCategories.code.TensorNondegen.EvalCoevalArg
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u


noncomputable section

/-- Nondegeneracy of the tensor product in an abelian monoidal category: tensoring with self
detects zero, and the right dual is zero iff the object is zero. -/
class TensorNondegenerate (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Abelian C] : Prop where
  isZero_of_tensor_self_isZero : ∀ (X : C), IsZero (X ⊗ X) → IsZero X
  isZero_rightDual_of_isZero : ∀ (X : C) [HasRightDual X], IsZero X → IsZero (Xᘁ)
  isZero_of_isZero_rightDual : ∀ (X : C) [HasRightDual X], IsZero (Xᘁ) → IsZero X

end
