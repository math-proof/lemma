/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopGeometricDualWeighted
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls

noncomputable section

def kwg_pathDefectCount (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) (F : Finset (kwg_Edge P)) : Nat :=
  (kwg_pathEdgeIndices P path).countP fun edge => decide (edge ∈ F)


def kwg_pathDefectSign (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) (F : Finset (kwg_Edge P)) : Real :=
  if Even (kwg_pathDefectCount P path F) then 1 else -1


end
end StatMech.Onsager
