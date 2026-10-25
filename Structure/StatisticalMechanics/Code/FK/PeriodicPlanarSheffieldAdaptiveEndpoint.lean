/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.EndpointBridgedRectangleArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B
  dualArcBound : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B
  startA : Nat -> Real
  startB : Nat -> Real
  startC : Nat -> Real
  startD : Nat -> Real
  lowerA : Nat -> Real
  lowerB : Nat -> Real
  lowerC : Nat -> Real
  lowerD : Nat -> Real
  upperA : Nat -> Real
  upperB : Nat -> Real
  upperC : Nat -> Real
  upperD : Nat -> Real
  endA : Nat -> Real
  endB : Nat -> Real
  endC : Nat -> Real
  endD : Nat -> Real
  startSpanX : forall n, startA n + 5 * B < startB n - 5 * B
  startSpanY : forall n, startC n + 5 * B < startD n - 5 * B
  lowerSpanX : forall n, lowerA n + 5 * B < lowerB n - 5 * B
  lowerSpanY : forall n, lowerC n + 5 * B < lowerD n - 5 * B
  upperSpanX : forall n, upperA n + 5 * B < upperB n - 5 * B
  upperSpanY : forall n, upperC n + 5 * B < upperD n - 5 * B
  endSpanX : forall n, endA n + 5 * B < endB n - 5 * B
  endSpanY : forall n, endC n + 5 * B < endD n - 5 * B
  verticalStart : Tendsto (fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (startA n + 4 * B) (startB n - 4 * B) (startC n) (startD n)))
    atTop (nhds 1)
  horizontalEnd : Tendsto (fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (endA n) (endB n) (endC n + 4 * B) (endD n - 4 * B)))
    atTop (nhds 1)
  startBridge : Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (startA n) (startB n) (startC n + 4 * B) (startD n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (lowerA n + 4 * B) (lowerB n - 4 * B) (lowerC n) (lowerD n))))
    atTop (nhds 1)
  coreAdjacent : Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (lowerA n) (lowerB n) (lowerC n + 4 * B) (lowerD n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (upperA n + 4 * B) (upperB n - 4 * B) (upperC n) (upperD n))))
    atTop (nhds 1)
  endBridge : Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (upperA n) (upperB n) (upperC n + 4 * B) (upperD n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (endA n + 4 * B) (endB n - 4 * B) (endC n) (endD n))))
    atTop (nhds 1)
  dualStart : Tendsto (fun n => max
    ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      (startA n + 4 * B) (startB n - 4 * B) (startC n) (startD n)))
    ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
      (startA n) (startB n) (startC n + 4 * B) (startD n - 4 * B))))
    atTop (nhds 1)
  dualLower : Tendsto (fun n => max
    ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      (lowerA n + 4 * B) (lowerB n - 4 * B) (lowerC n) (lowerD n)))
    ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
      (lowerA n) (lowerB n) (lowerC n + 4 * B) (lowerD n - 4 * B))))
    atTop (nhds 1)
  dualUpper : Tendsto (fun n => max
    ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      (upperA n + 4 * B) (upperB n - 4 * B) (upperC n) (upperD n)))
    ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
      (upperA n) (upperB n) (upperC n + 4 * B) (upperD n - 4 * B))))
    atTop (nhds 1)
  dualEnd : Tendsto (fun n => max
    ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      (endA n + 4 * B) (endB n - 4 * B) (endC n) (endD n)))
    ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
      (endA n) (endB n) (endC n + 4 * B) (endD n - 4 * B))))
    atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
