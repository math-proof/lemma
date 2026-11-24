module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part15
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part2
open Finset Set
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def triHexPlanarFiniteStarBoundaryReachIndicator (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) : Real :=
  if ∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteStarGraph n)
        (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
          (Sum.inr (triHexPlanarFiniteTerminalMap n
            (triHexPlanarFiniteRootCell n) 0)) (Sum.inr y) then 1 else 0

end
end StatMech.FK.PeriodicPlanar
