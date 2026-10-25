/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeAxisBridge.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_axisOrContactCounterexampleEdge : Sym2 (Site 2) :=
  s(![-1, 0], ![0, 0])


def rlc_axisOrContactCounterexampleConfig :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e = rlc_axisOrContactCounterexampleEdge then true else false

end Universality
end StatMech
