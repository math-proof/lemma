/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.primalHalfPlaneBarrierReady
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) : Prop :=
  ∃ a b C D : Real, a < b ∧ C < D ∧
    ∃ xl xu xj : V,
    ∃ lower : P.graph.Walk xl xj,
    ∃ upper : P.graph.Walk xu xj,
      ¬ lower.Nil ∧ ¬ upper.Nil ∧
      (∀ {x y : V}, s(x, y) ∈ lower.edges → omega s(x, y) = true) ∧
      (∀ {x y : V}, s(x, y) ∈ upper.edges → omega s(x, y) = true) ∧
      E.vertexCoord xl 1 < C ∧ D < E.vertexCoord xu 1 ∧
      (∀ t : unitInterval,
        a < E.coordinates (E.walkArc lower t) 0 ∧
          E.coordinates (E.walkArc lower t) 0 < b) ∧
      (∀ t : unitInterval,
        a < E.coordinates (E.walkArc upper t) 0 ∧
          E.coordinates (E.walkArc upper t) 0 < b)


end StatMech.FK.PeriodicPlanar
