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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexNoAdjacentTransferInfinity (N n : Nat) :
    Matrix (SixVertexNoAdjacentSector N n)
      (SixVertexNoAdjacentSector N n) Real :=
  fun x y => sixVertexSectorTransferInfinity N n x.1 y.1

end
end StatMech.FrontierD
