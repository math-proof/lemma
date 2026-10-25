/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part8
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.RecursiveRectangleArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B
  dualArcBound : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B
  a : Nat → Nat → Real
  b : Nat → Nat → Real
  c : Nat → Nat → Real
  d : Nat → Nat → Real
  K : Nat → Nat
  spanX : ∀ n k, a n k + 5 * B < b n k - 5 * B
  spanY : ∀ n k, c n k + 5 * B < d n k - 5 * B
  verticalStart : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a n 0 + 4 * B) (b n 0 - 4 * B) (c n 0) (d n 0)))
    atTop (nhds 1)
  horizontalEnd : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a n (K n + 1)) (b n (K n + 1))
      (c n (K n + 1) + 4 * B) (d n (K n + 1) - 4 * B)))
    atTop (nhds 1)
  primalAdjacent : ∀ k : Nat → Nat, (∀ n, k n < K n + 1) →
    Tendsto (fun n ↦ max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a n (k n)) (b n (k n))
        (c n (k n) + 4 * B) (d n (k n) - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a n (k n + 1) + 4 * B) (b n (k n + 1) - 4 * B)
        (c n (k n + 1)) (d n (k n + 1))))) atTop (nhds 1)
  dualLevels : ∀ k : Nat → Nat, (∀ n, k n ≤ K n + 1) →
    Tendsto (fun n ↦ max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a n (k n) + 4 * B) (b n (k n) - 4 * B)
          (c n (k n)) (d n (k n))))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a n (k n)) (b n (k n))
          (c n (k n) + 4 * B) (d n (k n) - 4 * B)))) atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
