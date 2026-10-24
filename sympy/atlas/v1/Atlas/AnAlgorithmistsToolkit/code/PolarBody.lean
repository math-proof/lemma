/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PolarBody.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.Separation

open RealInnerProductSpace

namespace ConvexGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def polarBody (K : Set E) : Set E :=
  { y : E | ∀ x ∈ K, ⟪y, x⟫ ≤ 1 }
