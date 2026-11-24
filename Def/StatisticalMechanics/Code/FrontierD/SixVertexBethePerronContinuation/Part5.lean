module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part4
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

def sixVertexNoAdjacentInfinityGraph (N n : Nat) :
    SimpleGraph (SixVertexNoAdjacentSector N n) :=
  (sixVertexInfinityGraph N n).induce
    {x | SixVertexSectorNoAdjacent x}

end
end StatMech.FrontierD
