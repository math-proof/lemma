/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRawNonbacktrackingSimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveVertexConnector.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple


namespace StatMech.FrontierA

open scoped Convex

open Set

structure KWRawNonbacktrackingSimpleData
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ) : Prop where
  three_le : 3 ≤ n
  edge_ne_zero : ∀ i : Fin n, kwRawEdge vertex i ≠ 0
  previous_not_between : ∀ i : Fin n,
    ¬Sbtw ℝ (vertex (i + 1)) (vertex i) (vertex (i + 2))
  adjacent_disjoint : ∀ i : Fin n,
    Disjoint
      {z : ℂ | Sbtw ℝ (vertex i) z (vertex (i + 1))}
      {z : ℂ | Sbtw ℝ (vertex (i + 1)) z (vertex (i + 2))}
  nonincident_disjoint : ∀ i j : Fin n, KWEdgesNonincident i j →
    Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)

end StatMech.FrontierA
