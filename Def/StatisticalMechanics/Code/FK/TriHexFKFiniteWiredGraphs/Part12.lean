/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part10
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

def triHexPlanarFiniteStarSectorGraph (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    SimpleGraph (TriHexPlanarFiniteTerminal n) :=
  triHexFKTerminalSectorGraph (triHexPlanarFiniteTerminalMap n)
    (fun z => starFKLocalConnectivity
      (triHexPlanarFiniteStarConfigEquiv n omega z))


def triHexPlanarFiniteStarRepresentative (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    TriHexPlanarFiniteStarVertex n → TriHexPlanarFiniteTerminal n
  | Sum.inr v => v
  | Sum.inl z => triHexPlanarFiniteTerminalMap n z
      (starFKRepresentativeDirection
        (triHexPlanarFiniteStarConfigEquiv n omega z))


end
end StatMech.FK.PeriodicPlanar
