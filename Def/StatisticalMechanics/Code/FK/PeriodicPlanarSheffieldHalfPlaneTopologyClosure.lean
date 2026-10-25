/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTopologyClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part9
open MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

def threeCrossingCageEvent
    (D : PeriodicPlanarDualPair P Pdual)
    (B r R C D0 A Tbottom Ttop : Real) :
    Set (ConfigSpace (Sym2 V)) :=
  D.primalEmbedding.verticalCrossingEvent
      (A + 4 * B) (R - 4 * B) (C - 4 * B) (D0 + 4 * B) ∩
    D.primalEmbedding.horizontalCrossingEvent
      (r - 5 * B) (R + 5 * B) (C + 4 * B) (Tbottom - 4 * B) ∩
    D.primalEmbedding.horizontalCrossingEvent
      (r - 5 * B) (R + 5 * B) (Ttop + 4 * B) (D0 - 4 * B)


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
