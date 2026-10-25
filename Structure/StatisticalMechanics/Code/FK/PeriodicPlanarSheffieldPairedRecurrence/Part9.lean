/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part11
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate
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
  a : Nat -> Nat -> Real
  b : Nat -> Nat -> Real
  c : Nat -> Nat -> Real
  d : Nat -> Nat -> Real
  spanX : forall k n, a k n + 5 * B < b k n - 5 * B
  spanY : forall k n, c k n + 5 * B < d k n - 5 * B
  verticalStart : Tendsto (fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n)))
    atTop (nhds 1)
  horizontalLevel : forall k, Tendsto (fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a (k + 1) n) (b (k + 1) n)
      (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B)))
    atTop (nhds 1)
  primalLevel : forall k, Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B)
      (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1)
  dualLevel : forall k, Tendsto (fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))))
    atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
