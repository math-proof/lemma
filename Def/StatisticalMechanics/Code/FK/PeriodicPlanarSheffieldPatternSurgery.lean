/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualBurtonKeane.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldWholeArcCrosscut.Part3
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

def primalDualPatternSupport
    (D : PeriodicPlanarDualPair P Pdual)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W)) :
    Finset (Sym2 V) :=
  primal ∪ dual.map D.edgeDual.symm.toEmbedding


def primalDualOpenPattern
    (D : PeriodicPlanarDualPair P Pdual)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W)) :
    ConfigSpace ↑(D.primalDualPatternSupport primal dual) :=
  fun e => decide (e.1 ∈ primal)


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
