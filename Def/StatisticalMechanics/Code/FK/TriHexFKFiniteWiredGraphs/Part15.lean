/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part13
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

def triHexPlanarFiniteStarVertexComponentLabel (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    TriHexPlanarFiniteStarVertex n →
      (triHexPlanarFiniteStarWiredSectorGraph n omega).ConnectedComponent ⊕
        TriHexPlanarFiniteStarIsolatedCenter n omega
  | Sum.inr v => Sum.inl
      ((triHexPlanarFiniteStarWiredSectorGraph n omega).connectedComponentMk v)
  | Sum.inl z => if h : triHexPlanarFiniteStarConfigEquiv n omega z =
        (false, false, false) then
      Sum.inr ⟨z, h⟩
    else
      Sum.inl ((triHexPlanarFiniteStarWiredSectorGraph n omega).connectedComponentMk
        (triHexPlanarFiniteStarRepresentative n omega (Sum.inl z)))


end
end StatMech.FK.PeriodicPlanar
