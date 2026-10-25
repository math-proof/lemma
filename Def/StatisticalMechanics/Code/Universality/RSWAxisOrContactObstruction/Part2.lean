/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeAxisBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_reflectedFailureAnchorEdge (t : ℤ) : Sym2 (Site 2) :=
  s(![-1, t + 1], ![0, t + 1])


def rlc_singleClosedFailureAnchorConfig (t : ℤ) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e = s(![0, t], ![0, t + 1]) then false else true


end Universality
end StatMech
