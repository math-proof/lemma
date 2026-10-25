/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageShells
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc_latticeconnected.Part2
open Filter Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.FK StatMech.FK.PeriodicPlanar StatMech.Lattice

open StatMech.Percolation StatMech.ConfigSpace

noncomputable section

def fkQgt4SquarePeriodicConnectionShellPairs (n : Nat) :
    Finset (square.BufferedVertex (2 * n) × square.BufferedVertex (2 * n)) :=
  (square.orbitShellCandidatePairs (2 * n)).filter
    (fun xy => n ≤ square.graph.dist xy.1.1 xy.2.1)

end
end StatMech.FrontierD
