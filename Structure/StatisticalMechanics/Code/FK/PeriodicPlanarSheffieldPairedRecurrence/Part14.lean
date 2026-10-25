/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part21
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure PairedAdjacentOutwardScheduleData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (step : Nat -> Int) (pad : Nat -> Int) where
  base : PairedAdjacentBoundaryBandScheduleData
    E Edual mu muDual step
  outwardRadiusDual : Nat -> Nat
  outwardContinuationDual :
    Edual.UniformOutwardBoundaryCrossingRadius
      muDual pad outwardRadiusDual
  schedule : forall m, PairedAlignedMarginSchedule E Edual
    (base.family m) (base.familyDual m)
    (fun _ => max
      (E.connectorMarginRequirement (base.radius m))
      (Edual.connectorMarginRequirement (outwardRadiusDual m)))
    (fun _ => max
      (E.connectorMarginRequirement (base.radius m))
      (Edual.connectorMarginRequirement (outwardRadiusDual m)))


end StatMech.FK.PeriodicPlanar
