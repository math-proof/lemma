/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PairedAdjacentCrossNestedOutwardData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (pad : Nat -> Int) (padding : Nat) where
  dualRadius : Nat -> Nat
  dualOutward :
    forall (k extentX extentY : Nat -> Nat)
      (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores
        E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
        (scheduleData.score n) (scheduleData.scoreDual n)
        (scheduleData.family n) (scheduleData.familyDual n)
        (scheduleData.schedule n) (k n) (extentX n) (extentY n)),
      (forall n, PairedAlignedConnectorSlack E Edual
        (scheduleData.family n) (scheduleData.familyDual n)
        (scheduleData.schedule n) (max (dualRadius n) n) (k n)) ->
      Tendsto (fun n => max
        (muDual.real (Edual.verticalCrossingEvent
          (exact n).raw.data.wideLeft (exact n).raw.data.wideRight
          (0 - (pad n : Real)) ((extentY n : Real) + pad n)))
        (muDual.real (Edual.horizontalCrossingEvent
          (0 - (pad n : Real)) ((extentX n : Real) + pad n)
          0 (extentY n)))) atTop (nhds 1)
  index : Nat -> Nat
  slack : forall n, PairedAlignedConnectorSlack E Edual
    (scheduleData.family n) (scheduleData.familyDual n)
    (scheduleData.schedule n)
    (max (max (scheduleData.radius n) (dualRadius n)) n) (index n)
  triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
    E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
    (scheduleData.score n) (scheduleData.scoreDual n)
    (scheduleData.family n) (scheduleData.familyDual n)
    (scheduleData.schedule n) (index n) padding


end StatMech.FK.PeriodicPlanar
