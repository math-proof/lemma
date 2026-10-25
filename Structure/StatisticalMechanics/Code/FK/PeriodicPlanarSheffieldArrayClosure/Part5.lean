/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part10
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.PointwiseMacroArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Nat
  T : Nat
  Bpos : 0 < B
  increment : 8 * B < T
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
  spanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B
  verticalStart : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
    atTop (nhds 1)
  horizontalLevel :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    ∀ k, Tendsto (fun n ↦ mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (q n (k + 1)).1 (q n (k + 1)).2.1
        ((q n (k + 1)).2.2.1 + 4 * B)
        ((q n (k + 1)).2.2.2 - 4 * B))) atTop (nhds 1)
  primalLevel :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    ∀ k, Tendsto (fun n ↦ max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (q n k).1 (q n k).2.1
        ((q n k).2.2.1 + 4 * B) ((q n k).2.2.2 - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (q n k).1 (q n k).2.1 ((q n k).2.2.1 + 4 * B)
        ((q n k).2.2.2 - 4 * B + (T + 4 * B : Nat)))))
      atTop (nhds 1)
  dualLevel :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    ∀ k, Tendsto (fun n ↦ max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          ((q n k).1 + 4 * B) ((q n k).2.1 - 4 * B)
          ((q n k).2.2.1) ((q n k).2.2.2)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          ((q n k).1) ((q n k).2.1)
          ((q n k).2.2.1 + 4 * B) ((q n k).2.2.2 - 4 * B))))
      atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
