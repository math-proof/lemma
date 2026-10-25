/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part14
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

noncomputable instance triHexPlanarFiniteStarIsolatedCenterFintype
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    Fintype (TriHexPlanarFiniteStarIsolatedCenter n omega) :=
  @Subtype.fintype (TriHexPlanarFiniteCell n)
    (fun z => triHexPlanarFiniteStarConfigEquiv n omega z =
      (false, false, false)) inferInstance inferInstance


end
end StatMech.FK.PeriodicPlanar
