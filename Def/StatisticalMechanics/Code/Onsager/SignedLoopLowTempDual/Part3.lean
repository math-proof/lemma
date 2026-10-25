/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopGeometricDualWeighted
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls

noncomputable section

def kwg_lowTempPathDualSum (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v) : Real :=
  ∑ F : Finset (kwg_Edge P),
    if kwg_IsEven (kwg_dualEnds P) F then
      kwg_pathDefectSign P path F * Real.exp (-2 * beta) ^ F.card
    else 0


def kwg_lowTempDualSum (P : PlanarZ2Subgraph) (beta : Real) : Real :=
  ∑ F : Finset (kwg_Edge P),
    if kwg_IsEven (kwg_dualEnds P) F then
      Real.exp (-2 * beta) ^ F.card
    else 0

end
end StatMech.Onsager
