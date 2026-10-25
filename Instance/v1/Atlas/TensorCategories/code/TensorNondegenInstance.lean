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
import Class.v1.Atlas.TensorCategories.code.TensorNondegenInstance
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u


noncomputable section

section Instance

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]

/-- Any rigid braided abelian monoidal preadditive category has a nondegenerate tensor product. -/
instance tensorNondegenerate_of_rigidCategory : TensorNondegenerate C where
  isZero_of_tensor_self_isZero := TensorNondegen.isZero_of_tensorSelf_isZero
  isZero_rightDual_of_isZero := fun _ _ h => CategoryTheory.isZero_rightDual_of_isZero h
  isZero_of_isZero_rightDual := fun _ _ h => CategoryTheory.isZero_of_isZero_rightDual h

end Instance
end
