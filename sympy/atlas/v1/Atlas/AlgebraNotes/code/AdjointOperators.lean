/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/AdjointOperators.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace AdjointOperators

open scoped InnerProductSpace
open LinearMap Submodule

def IsNormalOperator {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) : Prop :=
  T ∘ₗ LinearMap.adjoint T = LinearMap.adjoint T ∘ₗ T
