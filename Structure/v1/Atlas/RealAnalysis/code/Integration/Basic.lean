/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Def.v1.Atlas.RealAnalysis.code.Integration.Basic


namespace Integration

/-- A partition of the closed interval `[a,b]`: a strictly increasing finite sequence
`a = x_0 < x_1 < ⋯ < x_n = b` of points. The field `n` is the number of subintervals,
and `points` enumerates the `n + 1` endpoints. -/
structure Partition (a b : ℝ) where
  n : ℕ
  points : Fin (n + 1) → ℝ
  ordered : StrictMono points
  first : points 0 = a
  last : points (Fin.last n) = b

variable {a b : ℝ}

/-- A tagged partition of `[a,b]`: a partition together with a choice of a tag
`ξ_k ∈ [x_{k-1}, x_k]` in each subinterval. -/
structure TaggedPartition (a b : ℝ) extends Partition a b where
  tags : Fin n → ℝ
  tag_mem : ∀ i : Fin n, points i.castSucc ≤ tags i ∧ tags i ≤ points i.succ

end Integration
