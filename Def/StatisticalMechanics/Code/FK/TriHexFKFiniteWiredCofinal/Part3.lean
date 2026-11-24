module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part3
open Finset Set SimpleGraph Filter MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def triHexPlanarFiniteTriangleInducedBoundaryReachIndicator (n : Nat)
    (eta : ConfigSpace (triHexPlanarFiniteTriangleInducedGraph n).edgeSet) :
    Real :=
  if ∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteTriangleInducedGraph n)
        (extendActive (triHexPlanarFiniteTriangleInducedGraph n) eta)).Reachable
          (triHexPlanarFiniteTerminalMap n
            (triHexPlanarFiniteRootCell n) 0) y then 1 else 0


end
end StatMech.FK.PeriodicPlanar
