module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part2
open Finset Filter Matrix Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem sixVertexNoAdjacentInfinityGraph_adjMatrix :
    (sixVertexNoAdjacentInfinityGraph N n).adjMatrix Real =
      sixVertexNoAdjacentTransferInfinity N n := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [sixVertexNoAdjacentInfinityGraph, SimpleGraph.induce,
      sixVertexInfinityGraph, sixVertexNoAdjacentTransferInfinity,
      sixVertexSectorTransferInfinity]
  · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    simp [sixVertexNoAdjacentInfinityGraph, SimpleGraph.induce,
      sixVertexInfinityGraph, sixVertexNoAdjacentTransferInfinity,
      sixVertexSectorTransferInfinity, hxy, hval]
    rfl

end
end StatMech.FrontierD
