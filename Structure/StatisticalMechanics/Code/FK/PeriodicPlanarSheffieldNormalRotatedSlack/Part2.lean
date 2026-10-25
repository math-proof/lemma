/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNormalRotatedSlack.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure NormalTwoRotatedEndpointLimitData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W))) where
  score : Nat -> Real
  scoreDual : Nat -> Real
  family : forall n,
    E.NormalBoundaryBandFamily mu (P.orbitBox n) (score n)
  familyDual : forall n,
    Edual.NormalBoundaryBandFamily muDual
      (Pdual.orbitBox n) (scoreDual n)
  schedule : forall n, PairedAlignedMarginSchedule E Edual
    (family n) (familyDual n) (fun _ => 0) (fun _ => 0)
  index : Nat -> Nat
  level : forall n,
    AlignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
      (score n) (scoreDual n) (family n) (familyDual n)
      (schedule n) (index n)
  familyRotated : forall n,
    E.axisSwap.NormalBoundaryBandFamily mu
      (P.axisSwap.orbitBox n) (score n)
  familyDualRotated : forall n,
    Edual.axisSwap.NormalBoundaryBandFamily muDual
      (Pdual.axisSwap.orbitBox n) (scoreDual n)
  scheduleRotated : forall n,
    PairedAlignedMarginSchedule E.axisSwap Edual.axisSwap
      (familyRotated n) (familyDualRotated n)
      (fun _ => 0) (fun _ => 0)
  rotatedVerticalLevel : forall n,
    AlignedExactExtentPairedMixedBoundaryScores
      E.axisSwap Edual.axisSwap mu muDual
      (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
      (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
      (scheduleRotated n) (index n) (level n).normalY
      (level n).normalX
  rotatedHorizontalLevel : forall n,
    AlignedExactExtentPairedMixedBoundaryScores
      E.axisSwap Edual.axisSwap mu muDual
      (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
      (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
      (scheduleRotated n) (index n) (level n).rotatedHorizontalX
      (level n).rotatedHorizontalY
  rotatedVerticalLevel_heq : forall n,
    rotatedVerticalLevel n ≍ (level n).rotatedVertical
  rotatedHorizontalLevel_heq : forall n,
    rotatedHorizontalLevel n ≍ (level n).rotatedHorizontal
  normalLimit : Tendsto (fun n => max
    (mu.real (E.horizontalCrossingEvent
      0 (level n).normalX 0 (level n).normalY))
    (mu.real (E.verticalCrossingEvent
      (level n).normal.raw.data.wideLeft
      (level n).normal.raw.data.wideRight 0 (level n).normalY)))
    atTop (nhds 1)
  dualRotatedVerticalLimit : Tendsto (fun n => max
    (muDual.real (Edual.axisSwap.horizontalCrossingEvent
      0 (level n).normalY 0 (level n).normalX))
    (muDual.real (Edual.axisSwap.verticalCrossingEvent
      (rotatedVerticalLevel n).raw.data.wideLeft
      (rotatedVerticalLevel n).raw.data.wideRight 0 (level n).normalX)))
    atTop (nhds 1)
  dualRotatedHorizontalLimit : Tendsto (fun n => max
    (muDual.real (Edual.axisSwap.horizontalCrossingEvent
      0 (level n).rotatedHorizontalX 0
        (level n).rotatedHorizontalY))
    (muDual.real (Edual.axisSwap.verticalCrossingEvent
      (rotatedHorizontalLevel n).raw.data.wideLeft
      (rotatedHorizontalLevel n).raw.data.wideRight 0
        (level n).rotatedHorizontalY))) atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
