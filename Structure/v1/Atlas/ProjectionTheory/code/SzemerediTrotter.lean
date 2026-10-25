/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset Real


namespace SzemerediTrotter

/-- A line in $\mathbb{R}^2$: a $1$-dimensional non-empty affine subspace of $\mathbb{R}^2$. -/
structure Line2 where
  carrier : AffineSubspace ℝ (Fin 2 → ℝ)
  dim_eq : Module.finrank ℝ carrier.direction = 1
  nonempty : (carrier : Set (Fin 2 → ℝ)).Nonempty

end SzemerediTrotter
