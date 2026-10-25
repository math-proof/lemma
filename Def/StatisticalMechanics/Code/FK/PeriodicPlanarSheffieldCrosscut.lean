/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneBarrier
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms.Part2
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


noncomputable def PeriodicPlaneEmbedding.simpleWalkArc
    (E : PeriodicPlaneEmbedding P) :
    ∀ {x y : V}, P.graph.Walk x y → Path (E.vertex x) (E.vertex y)
  | _, _, .nil => Path.refl _
  | _, _, .cons h .nil => E.edgeArc h
  | _, _, .cons h (.cons h' p) =>
      (E.edgeArc h).trans (E.simpleWalkArc (.cons h' p))

end StatMech.FK.PeriodicPlanar
