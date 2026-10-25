/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOpenBoundarySource
open Filter MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P) (r R c d : Real)
    (L U : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
      (E.lowerBoundaryRayVertices r c) ∩
    E.infiniteOpenBoundaryConnectionTo r (U : Set V)
      (E.upperBoundaryRayVertices r d)) \
    E.halfPlanePairMergeErrorUnion R L U

end StatMech.FK.PeriodicPlanar
