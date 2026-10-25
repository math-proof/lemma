/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part3
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

def rlc_reflectedTargetLocallySupported {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2)) : Prop :=
  e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
    rlc_edgeBoxIncidentGap G (e.map rlc_flipX) ∨
    e ∈ rlc_reflectedPathEdges gamma.1 ∨
    e ∈ rlc_reflectedPathEdges gamma'.1


def rlc_boundarySourceLocallySupported {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2)) : Prop :=
  rlc_edgeBoxIncidentGap G e ∨
    e ∈ rlc_reflectedPathEdges gamma.1 ∨
    e ∈ rlc_reflectedPathEdges gamma'.1


end Universality
end StatMech
