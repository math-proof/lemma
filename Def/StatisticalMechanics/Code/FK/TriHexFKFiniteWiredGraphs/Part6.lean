/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part4
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

def triHexPlanarFiniteStarGraph (n : Nat) :
    SimpleGraph (TriHexPlanarFiniteStarVertex n) :=
  SimpleGraph.fromEdgeSet (Set.range (triHexPlanarFiniteStarEdge n))

end
end StatMech.FK.PeriodicPlanar
