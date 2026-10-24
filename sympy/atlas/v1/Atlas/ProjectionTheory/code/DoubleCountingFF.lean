/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingFF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ProjectionTheory

open Finset BigOperators

/-- The projection in direction `θ` of a point `(x₁, x₂) ∈ F × F`, defined as
`π_θ(x) = x₁ + θ · x₂`. -/
def piTheta {F : Type*} [Add F] [Mul F] (θ : F) : F × F → F :=
  fun x => x.1 + θ * x.2

/-- The image `π_θ(X) ⊆ F` of a finite set `X ⊆ F × F` under the direction-`θ` projection
`piTheta θ`. -/
noncomputable def projectionImage {F : Type*} [Add F] [Mul F] [DecidableEq F]
    (θ : F) (X : Finset (F × F)) : Finset F :=
  X.image (piTheta θ)
