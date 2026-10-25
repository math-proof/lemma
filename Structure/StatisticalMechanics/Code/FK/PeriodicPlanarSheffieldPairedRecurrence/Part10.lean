/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part12
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure PeriodicPlanarDualPair.ComplementaryCrossNestedLimitCertificate
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
  a0 : Nat -> Real
  b0 : Nat -> Real
  c0 : Nat -> Real
  d0 : Nat -> Real
  a1 : Nat -> Real
  b1 : Nat -> Real
  c1 : Nat -> Real
  d1 : Nat -> Real
  spanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B
  spanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B
  spanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B
  primalAdjacent : Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n))))
    atTop (nhds 1)
  dualVertical0 : Tendsto (fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
    atTop (nhds 1)
  dualHorizontal1 : Tendsto (fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B)))
    atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
