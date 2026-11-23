/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_34_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor

@[expose] public section


open TensorCategories in
abbrev Definition_1_34_1_NormalizedQuasiFiberFunctor := @QuasiFiberFunctor.IsNormalized

