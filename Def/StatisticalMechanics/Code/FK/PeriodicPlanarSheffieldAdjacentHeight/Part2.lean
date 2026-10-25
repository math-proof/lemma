/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdjacentHeight.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

def sheffieldMacroArrayCoordinates (B T : Nat)
    (a0 b0 c0 d0 : Nat → Real) (n k : Nat) : Real × Real × Real × Real :=
  (a0 n - 4 * B * k,
    b0 n + 4 * B * k,
    c0 n + 4 * B * k,
    d0 n + T * k)


end StatMech.FK.PeriodicPlanar
