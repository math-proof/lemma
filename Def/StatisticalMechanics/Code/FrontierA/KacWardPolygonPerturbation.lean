/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction


namespace StatMech.FrontierA

open scoped Convex

open Set

def kwRawEdge {n : ℕ} [NeZero n] (vertex : Fin n → ℂ)
    (i : Fin n) : ℂ :=
  vertex (i + 1) - vertex i

def kwRawClosedEdge {n : ℕ} [NeZero n] (vertex : Fin n → ℂ)
    (i : Fin n) : Set ℂ :=
  segment ℝ (vertex i) (vertex (i + 1))


end StatMech.FrontierA
