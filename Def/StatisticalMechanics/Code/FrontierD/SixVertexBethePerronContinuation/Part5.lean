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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part4
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexNoAdjacentInfinityGraph (N n : Nat) :
    SimpleGraph (SixVertexNoAdjacentSector N n) :=
  (sixVertexInfinityGraph N n).induce
    {x | SixVertexSectorNoAdjacent x}

end
end StatMech.FrontierD
