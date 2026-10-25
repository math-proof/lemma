/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotatedBoundaryBands.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.VariablePadTwoLevelRectangleArray
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
  xPad0 : Nat → Real
  yPad0 : Nat → Real
  xPad1 : Nat → Real
  yPad1 : Nat → Real
  xPad0_ge : ∀ n, 4 * B ≤ xPad0 n
  yPad0_ge : ∀ n, 4 * B ≤ yPad0 n
  xPad1_ge : ∀ n, 4 * B ≤ xPad1 n
  yPad1_ge : ∀ n, 4 * B ≤ yPad1 n
  spanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B
  spanX1 : ∀ n, a1 n + 5 * B < b1 n - 5 * B
  spanY1 : ∀ n, c1 n + 5 * B < d1 n - 5 * B
  verticalStart : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
    atTop (nhds 1)
  horizontalEnd : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))
    atTop (nhds 1)
  primalAdjacent : Tendsto (fun n ↦ max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))))
    atTop (nhds 1)
  dualLevel0 : Tendsto (fun n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
    atTop (nhds 1)
  dualLevel1 : Tendsto (fun n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
    atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
