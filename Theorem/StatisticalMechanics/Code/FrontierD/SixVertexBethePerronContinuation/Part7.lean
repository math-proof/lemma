/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part7
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexNoAdjacentInfinityGraph_adj_alternating
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    (sixVertexNoAdjacentInfinityGraph N n).Adj
      (sixVertexNoAdjacentAlternatingEven N n hn hhalf)
      (sixVertexNoAdjacentAlternatingOdd N n hn hhalf) :=
  sixVertexInfinityGraph_adj_alternating hn hhalf


end
end StatMech.FrontierD
