/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/EuclideanProjectionBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace ProjectionTheory

/--
Data bundle for the Euclidean projection bound theorem: a scale parameter `R > 1`,
a point set `X` of cardinality `cardX`, a direction set `D` of cardinality `cardD`,
a uniform projection bound `S = max_{θ ∈ D} |π_θ(X)|`, and local covering numbers
`nX r`, `nD ρ` measuring the maximum number of points of `X` (resp. directions of `D`)
in any ball of radius `r` (resp. `ρ`), each bounded above by `cardX`, `cardD`.
-/
structure EuclideanProjectionData where
  R : ℝ
  hR : 1 < R
  cardX : ℕ
  hcardX : 0 < cardX
  cardD : ℕ
  hcardD : 0 < cardD
  S : ℕ
  hS : 0 < S
  nX : ℝ → ℕ
  nD : ℝ → ℕ
  hnX_le : ∀ r, (nX r : ℝ) ≤ cardX
  hnD_le : ∀ ρ, (nD ρ : ℝ) ≤ cardD

end ProjectionTheory
