/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundFF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace FourierBound

/-- Projection of `(x, y) ∈ F × F` onto the line of slope `θ`: `π_θ(x, y) = x + θ y`.
This is the standard projection used throughout finite-field projection theory. -/
def piSlope {F : Type*} [Ring F] (θ : F) : F × F → F := fun p => p.1 + θ * p.2

end FourierBound
