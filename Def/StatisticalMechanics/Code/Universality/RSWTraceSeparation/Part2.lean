/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWContactRedesign.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
import Theorem.StatisticalMechanics.Code.Universality.RSWTraceSeparation
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_outerExitWindingRegion {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Set (Site 2) :=
  jec_leftRegion
    ((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega)).mapLe (faceBoundaryGraph_le _))


def RlcOuterExitTraceWindingSplit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  RlcTracePreimageRegionSplit gamma.1
      (rlc_outerExitWindingRegion G omega) ∧
    RlcTracePreimageRegionSplit gamma'.1
      (rlc_outerExitWindingRegion G omega)


end Universality
end StatMech
