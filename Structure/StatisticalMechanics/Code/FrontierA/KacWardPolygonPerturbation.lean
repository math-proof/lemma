/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation


namespace StatMech.FrontierA

open scoped Convex

open Set

structure KWRawSimplePolygonData
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ) : Prop where
  three_le : 3 ≤ n
  vertex_injective : Function.Injective vertex
  cross_ne_zero : ∀ i : Fin n,
    kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0
  nonincident_disjoint : ∀ i j : Fin n, KWEdgesNonincident i j →
    Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)

end StatMech.FrontierA
