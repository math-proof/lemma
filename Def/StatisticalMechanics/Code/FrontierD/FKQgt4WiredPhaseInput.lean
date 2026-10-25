/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly.Part3
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
open MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

def originIncidentEdges (d : Nat) : Finset (Sym2 (Site d)) :=
  (hypercubicLattice d).neighborFinset (origin d) |>.image
    (fun x => s(origin d, x))


def originIncidentClosedPattern (d : Nat) :
    ConfigSpace (originIncidentEdges d) :=
  fun _ => false


def originIsolatedCylinder (d : Nat) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  cylinder (originIncidentEdges d) ({originIncidentClosedPattern d} :
    Set (ConfigSpace (originIncidentEdges d)))

end
end StatMech.FrontierD
