/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFaces.Part3
import Instance.StatisticalMechanics.Code.FK.TriHexBrickInnerFaces
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls

noncomputable section

noncomputable def triHexBrickFullDualGraph (m : Nat) :
    SimpleGraph (kwg_Face (triHexPlanarFiniteStarPlanar m)) :=
  BeffaraDC.pfdClosedDual (triHexPlanarFiniteStarPlanar m) ⊥

end
end StatMech.FK.PeriodicPlanar
