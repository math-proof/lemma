/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part7
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def PeriodicPlaneEmbedding.rectLeftBoundary
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (x : E.RectVertex a b c d) : Prop :=
  ∃ y : V, P.graph.Adj x.1 y ∧ E.vertexCoord y 0 < a

def PeriodicPlaneEmbedding.rectRightBoundary
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (x : E.RectVertex a b c d) : Prop :=
  ∃ y : V, P.graph.Adj x.1 y ∧ b < E.vertexCoord y 0

def PeriodicPlaneEmbedding.rectBottomBoundary
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (x : E.RectVertex a b c d) : Prop :=
  ∃ y : V, P.graph.Adj x.1 y ∧ E.vertexCoord y 1 < c

def PeriodicPlaneEmbedding.rectTopBoundary
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (x : E.RectVertex a b c d) : Prop :=
  ∃ y : V, P.graph.Adj x.1 y ∧ d < E.vertexCoord y 1

end StatMech.FK.PeriodicPlanar
