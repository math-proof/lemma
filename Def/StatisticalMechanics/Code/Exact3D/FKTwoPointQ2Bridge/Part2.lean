/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FreeWiredAgreeClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Theorem.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


def boxConnectionDetourEvent
    (d : ℕ) {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    Set (ConfigSpace (Sym2 (Lattice.Site d))) :=
  boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y) \
    boxConnEvent d n x y


end Exact3D
end StatMech
