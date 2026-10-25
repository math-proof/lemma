/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualCoordinates.Part4
import Theorem.StatisticalMechanics.Code.FK.FreeNestedDecreasing
open Filter Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

def triHexHexBufferedFaceDualInnerEvent (N n : Nat)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    Set (ConfigSpace (Sym2 (hexagonal.BufferedVertex n))) :=
  {rho | triHexFaceDualInnerActive N
    (hexagonal.extendEdge (hexagonal.bufferedRadius n) rho) ∈ A}


def triHexStarFaceDualInnerEvent
    {N m : Nat} (hNm : N < m)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    Set (ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex m))) :=
  {omega | triHexBrickDualInnerActiveRestrict hNm
    (triHexBrickPfdSupport m omega) ∈ A}

end
end StatMech.FK.PeriodicPlanar
