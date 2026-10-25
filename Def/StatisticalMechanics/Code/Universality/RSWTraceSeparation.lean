/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWContactRedesign.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcTracePreimagesSplit {a b c d n : ℤ}
    (gamma : RlcCrossingPath a b c d)
    (right : RlcRightDiagonalPath n) (left : RlcLeftDiagonalPath n) : Prop :=
  ∃ x ∈ rlc_pathVertices gamma, ∃ y ∈ rlc_pathVertices gamma,
    ((rlc_primalDualReflect.symm x ∈ rlc_pathVertices right.1 ∧
        rlc_primalDualReflect.symm y ∈ rlc_pathVertices left.1) ∨
      (rlc_primalDualReflect.symm x ∈ rlc_pathVertices left.1 ∧
        rlc_primalDualReflect.symm y ∈ rlc_pathVertices right.1))


def RlcLowestHighestTracePreimageSplit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  RlcTracePreimagesSplit gamma.1 gamma gamma' ∧
    RlcTracePreimagesSplit gamma'.1 gamma gamma'


def RlcTracePreimageRegionSplit {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) (K : Set (Site 2)) : Prop :=
  ∃ x ∈ rlc_pathVertices gamma, ∃ y ∈ rlc_pathVertices gamma,
    ((rlc_primalDualReflect.symm x ∈ K ∧
        rlc_primalDualReflect.symm y ∉ K) ∨
      (rlc_primalDualReflect.symm x ∉ K ∧
        rlc_primalDualReflect.symm y ∈ K))


end Universality
end StatMech
