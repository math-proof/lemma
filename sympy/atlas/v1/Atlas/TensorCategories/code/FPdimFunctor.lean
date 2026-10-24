/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Category.Atlas.v1.TensorCategories.code.Prop_1_45_10
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor

open Finset BigOperators FusionRing FusionRing.FPdimData

/-- A quasi-tensor functor between fusion rings induces a fusion ring homomorphism whose
matrix entries are nonnegative, reflecting the categorical positivity of multiplicities
under quasi-tensor functors. -/
