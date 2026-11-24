module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
public import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part3
open Filter MeasureTheory Set SimpleGraph Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable def PeriodicPlaneEmbedding.walkArc
    (E : PeriodicPlaneEmbedding P) :
    ∀ {x y : V}, P.graph.Walk x y → Path (E.vertex x) (E.vertex y)
  | _, _, .nil => Path.refl _
  | _, _, .cons h p => (E.edgeArc h).trans (E.walkArc p)

end StatMech.FK.PeriodicPlanar
