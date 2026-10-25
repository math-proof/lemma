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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part6
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexNoAdjacentAlternatingEven
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    SixVertexNoAdjacentSector N n :=
  ⟨sixVertexAlternatingEvenSector N n hhalf,
    sixVertexAlternatingEvenSector_noAdjacent hn hhalf⟩

def sixVertexNoAdjacentAlternatingOdd
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    SixVertexNoAdjacentSector N n :=
  ⟨sixVertexAlternatingOddSector N n hhalf,
    sixVertexAlternatingOddSector_noAdjacent hn hhalf⟩

end
end StatMech.FrontierD
