/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part16
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem PairedBoundaryBandLevel.primalAdjacent_limit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) (level : PairedBoundaryBandLevel data) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (level.a n) (level.b n) (level.c n) (level.d n)))
      (mu.real (E.verticalCrossingEvent
        (level.a n) (level.b n) (level.c n)
          (level.d n + step n)))) atTop (nhds 1) := by
  exact data.primalContinuation level.width level.height level.margin
    level.base level.a level.b level.c level.d data.score
    level.width_separated level.height_separated data.score_le_one
    data.score_tendsto level.primal_source_subset
    level.primal_connector_subset level.primal_bottom level.primal_top
    level.primal_left level.primal_right


theorem PairedBoundaryBandLevel.dual_limit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) (level : PairedBoundaryBandLevel data) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (level.a n) (level.b n) (level.c n) (level.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (level.a n) (level.b n) (level.c n) (level.d n))))
      atTop (nhds 1) := by
  exact data.dualContinuation level.widthDual level.heightDual
    level.marginDual level.baseDual level.a level.b level.c level.d
    data.scoreDual level.widthDual_separated level.heightDual_separated
    data.scoreDual_le_one data.scoreDual_tendsto
    level.dual_source_subset level.dual_connector_subset
    level.dual_bottom level.dual_top level.dual_left level.dual_right


end StatMech.FK.PeriodicPlanar
