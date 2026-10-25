/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part4
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

noncomputable def triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
    (n : Nat) (p q : Real) : Real :=
  ∑ eta : ConfigSpace
      (Sym2 (TriHexPlanarFiniteTerminal n)),
    triHexPlanarFiniteTriangleInducedBoundaryReachIndicator n
        (restrictActive (triHexPlanarFiniteTriangleInducedGraph n) eta) *
      wiredFkProb (triHexPlanarFiniteTriangleInducedGraph n)
        (triHexPlanarFiniteBoundary n) p q eta


end
end StatMech.FK.PeriodicPlanar
