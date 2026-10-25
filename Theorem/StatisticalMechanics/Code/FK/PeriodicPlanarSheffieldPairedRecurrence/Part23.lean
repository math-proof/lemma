/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part15
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem DualOutwardBoundaryBandLevel.crossing_limit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {step pad : Nat -> Int}
    (data : PairedAdjacentOutwardScheduleData
      E Edual mu muDual step pad)
    (level : DualOutwardBoundaryBandLevel data) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (level.a n) (level.b n)
        (level.c n - pad n) (level.d n + pad n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (level.a n - pad n) (level.b n + pad n)
        (level.c n) (level.d n)))) atTop (nhds 1) := by
  exact data.outwardContinuationDual level.width level.height
    level.width_pos level.height_pos level.base
    level.a level.b level.c level.d data.base.scoreDual
    data.base.scoreDual_tendsto data.base.scoreDual_le_one
    level.source_subset level.connector_vertical_lower
    level.connector_vertical_outer level.connector_horizontal_lower
    level.connector_horizontal_outer level.bottom level.top
    level.left level.right


end StatMech.FK.PeriodicPlanar
