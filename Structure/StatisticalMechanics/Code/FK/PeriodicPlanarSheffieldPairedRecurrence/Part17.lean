/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part24
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure PairedAdjacentBoundaryBandTransition
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) where
  lower : PairedBoundaryBandLevel data
  upper : PairedBoundaryBandLevel data
  upper_a : upper.a = lower.a
  upper_b : upper.b = lower.b
  upper_c : upper.c = lower.c
  upper_d : upper.d = fun n => lower.d n + step n


end StatMech.FK.PeriodicPlanar
