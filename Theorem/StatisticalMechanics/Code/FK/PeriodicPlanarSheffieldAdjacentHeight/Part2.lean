/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdjacentHeight
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

theorem sheffieldMacroIncrement_gt_eight_mul (B : Nat) :
    (8 : Real) * B < sheffieldMacroIncrement B := by
  simp [sheffieldMacroIncrement]


end StatMech.FK.PeriodicPlanar
