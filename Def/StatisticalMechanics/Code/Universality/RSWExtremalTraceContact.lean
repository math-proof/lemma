/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalTraceContact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWWindingSideObstruction
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcTraceReflectedBoundaryContact {a b c d : ℤ}
    (tau : RlcCrossingPath a b c d) (K : Set (Site 2)) : Prop :=
  ∃ x y : Site 2, s(x, y) ∈ rlc_pathEdges tau ∧
    bdEdge (rlc_reflectedPrimalRegion K) s(x, y)


def RlcLowestHighestReflectedBoundaryContact {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  RlcTraceReflectedBoundaryContact gamma.1
      (rlc_outerExitWindingRegion G omega) ∧
    RlcTraceReflectedBoundaryContact gamma'.1
      (rlc_outerExitWindingRegion G omega)


end Universality
end StatMech
