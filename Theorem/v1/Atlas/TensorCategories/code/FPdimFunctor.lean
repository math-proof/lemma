/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.Category.Atlas.v1.TensorCategories.code.Prop_1_45_10
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor

@[expose] public section

open Finset BigOperators FusionRing FusionRing.FPdimData

/-- A quasi-tensor functor between fusion rings induces a fusion ring homomorphism whose
matrix entries are nonnegative, reflecting the categorical positivity of multiplicities
under quasi-tensor functors. -/


