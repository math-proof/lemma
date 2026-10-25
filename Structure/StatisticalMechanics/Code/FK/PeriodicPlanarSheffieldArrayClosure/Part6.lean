/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part11
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.TwoLevelBoundaryScoreArray
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) (B : Real) where
  Bpos : 0 < B
  primalArcBound : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B
  dualArcBound : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B
  a0 : Nat → Real
  b0 : Nat → Real
  c0 : Nat → Real
  d0 : Nat → Real
  a1 : Nat → Real
  b1 : Nat → Real
  c1 : Nat → Real
  d1 : Nat → Real
  spanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B
  spanX1 : ∀ n, a1 n + 5 * B < b1 n - 5 * B
  spanY1 : ∀ n, c1 n + 5 * B < d1 n - 5 * B
  bottomSource : Nat → Finset V
  topSource : Nat → Finset V
  leftSource : Nat → Finset V
  rightSource : Nat → Finset V
  bottomLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectSideConnectionEvent
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)
      (bottomSource n : Set V)
      (D.primalEmbedding.rectBottomBoundaryVertices
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n))))
    atTop (nhds 1)
  topLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectSideConnectionEvent
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)
      (topSource n : Set V)
      (D.primalEmbedding.rectTopBoundaryVertices
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n))))
    atTop (nhds 1)
  verticalMergeLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectanglePairMergeErrorUnion
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)
      (bottomSource n) (topSource n))) atTop (nhds 0)
  leftLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectSideConnectionEvent
      (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B)
      (leftSource n : Set V)
      (D.primalEmbedding.rectLeftBoundaryVertices
        (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B))))
    atTop (nhds 1)
  rightLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectSideConnectionEvent
      (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B)
      (rightSource n : Set V)
      (D.primalEmbedding.rectRightBoundaryVertices
        (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B))))
    atTop (nhds 1)
  horizontalMergeLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectanglePairMergeErrorUnion
      (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B)
      (leftSource n) (rightSource n))) atTop (nhds 0)
  primalAdjacent : Tendsto (fun n ↦ max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n))))
    atTop (nhds 1)
  dualLevel0 : Tendsto (fun n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B))))
    atTop (nhds 1)
  dualLevel1 : Tendsto (fun n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B))))
    atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
