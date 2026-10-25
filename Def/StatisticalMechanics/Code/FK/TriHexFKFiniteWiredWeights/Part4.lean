/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part15
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part3
open Finset Set
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

noncomputable def triHexPlanarFiniteTriangleWiredBoundaryProbability
    (n : Nat) (p q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 (TriHexPlanarFiniteTerminal n)),
    triHexPlanarFiniteTriangleBoundaryReachIndicator n
        (restrictActive (triHexPlanarFiniteTriangleGraph n) omega) *
      wiredFkProb (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q omega


noncomputable def triHexPlanarFiniteStarWiredBoundaryProbability
    (n : Nat) (p q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex n)),
    triHexPlanarFiniteStarBoundaryReachIndicator n
        (restrictActive (triHexPlanarFiniteStarGraph n) omega) *
      wiredFkProb (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q omega


end
end StatMech.FK.PeriodicPlanar
