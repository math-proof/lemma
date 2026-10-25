/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part25
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure PeriodicPlanarDualPair.PaddedPairedAdjacentTransition
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    {step pad : Nat -> Int}
    (data : PairedAdjacentOutwardScheduleData D.primalEmbedding
      D.dualEmbedding mu (D.dualMeasure mu) step pad) where
  primal : PairedAdjacentBoundaryBandTransition data.base
  dualLower : DualOutwardBoundaryBandLevel data
  dualUpper : DualOutwardBoundaryBandLevel data
  a0 : Nat -> Real
  b0 : Nat -> Real
  c0 : Nat -> Real
  d0 : Nat -> Real
  a1 : Nat -> Real
  b1 : Nat -> Real
  c1 : Nat -> Real
  d1 : Nat -> Real
  primalLower_a : primal.lower.a = a0
  primalLower_b : primal.lower.b = b0
  primalLower_c : primal.lower.c = fun n => c0 n + (pad n : Real)
  primalLower_d : primal.lower.d = fun n => d0 n - (pad n : Real)
  primalUpper_a : primal.upper.a = fun n => a1 n + (pad n : Real)
  primalUpper_b : primal.upper.b = fun n => b1 n - (pad n : Real)
  primalUpper_c : primal.upper.c = c1
  primalUpper_d : primal.upper.d = d1
  dualLower_a : dualLower.a = fun n => a0 n + (pad n : Real)
  dualLower_b : dualLower.b = fun n => b0 n - (pad n : Real)
  dualLower_c : dualLower.c = fun n => c0 n + (pad n : Real)
  dualLower_d : dualLower.d = fun n => d0 n - (pad n : Real)
  dualUpper_a : dualUpper.a = fun n => a1 n + (pad n : Real)
  dualUpper_b : dualUpper.b = fun n => b1 n - (pad n : Real)
  dualUpper_c : dualUpper.c = fun n => c1 n + (pad n : Real)
  dualUpper_d : dualUpper.d = fun n => d1 n - (pad n : Real)
  verticalStart : Tendsto (fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 n + pad n) (b0 n - pad n) (c0 n) (d0 n)))
    atTop (nhds 1)
  horizontalEnd : Tendsto (fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a1 n) (b1 n) (c1 n + pad n) (d1 n - pad n)))
    atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
