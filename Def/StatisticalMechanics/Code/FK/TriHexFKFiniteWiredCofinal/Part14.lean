module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part14
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

def triHexPlanarFiniteTriangleRootBoundaryEvent (n : Nat) :
    Set (ConfigSpace (Sym2 (TriHexPlanarFiniteTerminal n))) :=
  finiteRootBoundaryEvent (triHexPlanarFiniteTriangleInducedGraph n)
    (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTriangleRoot n)

def triHexPlanarTriBufferedRootBoundaryEvent (n : Nat) :
    Set (ConfigSpace (Sym2 (triangular.BufferedVertex (n + 1)))) :=
  finiteRootBoundaryEvent (triangular.bufferedGraph (n + 1))
    (triangular.bufferedBoundary (n + 1))
    (triHexPlanarTriBufferedRoot n)

end
end StatMech.FK.PeriodicPlanar
