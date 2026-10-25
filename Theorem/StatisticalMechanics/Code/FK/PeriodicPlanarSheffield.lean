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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


@[simp] theorem PeriodicPlaneEmbedding.vertexCoord_shift
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (x : V) (i : Fin 2) :
    E.vertexCoord (P.shift z x) i = E.vertexCoord x i + z i := by
  rw [PeriodicPlaneEmbedding.vertexCoord, E.vertex_shift,
    map_add]
  change E.coordinates (E.vertex x) i + E.coordinates (E.period z) i =
    E.vertexCoord x i + z i
  rw [E.coordinates_period]
  rfl


end StatMech.FK.PeriodicPlanar
