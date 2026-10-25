/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset


namespace ProjectionTheory

/-- Projection map over `ZMod p`: `projMap p θ (x₁, x₂) = x₁ + θ · x₂`, the
direction-`θ` projection in the affine plane `𝔽_p²`. -/
noncomputable def projMap (p : ℕ) (θ : ZMod p) (x : ZMod p × ZMod p) : ZMod p :=
  x.1 + θ * x.2

/-- The image `π_θ(X) ⊆ 𝔽_p` of a finite set `X ⊆ 𝔽_p²` under the projection
`projMap p θ`. -/
noncomputable def projImage (p : ℕ) (θ : ZMod p) (X : Finset (ZMod p × ZMod p)) :
    Finset (ZMod p) :=
  X.image (projMap p θ)

end ProjectionTheory
