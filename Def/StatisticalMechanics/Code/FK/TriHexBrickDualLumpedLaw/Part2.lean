module
public import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualBundles
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw.Part3
public import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualLumpedLaw
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

def triHexBrickPfdSupport (m : Nat)
    (omega : ConfigSpace
      (Sym2 (triHexPlanarFiniteStarPlanar m).V)) :
    ConfigSpace (triHexBrickFullDualGraph m).edgeSet :=
  pfdIndexedSupportActive (triHexPlanarFiniteStarPlanar m)
    (pfdEdgeComplement (triHexPlanarFiniteStarPlanar m)
      (restrictActive (triHexPlanarFiniteStarPlanar m).G omega))

end
end StatMech.FK.PeriodicPlanar
