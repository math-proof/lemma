/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotatedBoundaryBands.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualBoundaryBands.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

@[simp] theorem siteAxisSwap_horizontalShift (t : Int) :
    siteAxisSwap (horizontalShift t) = verticalShift t := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem siteAxisSwap_verticalShift (t : Int) :
    siteAxisSwap (verticalShift t) = horizontalShift t := by
  ext i
  fin_cases i <;> rfl


end StatMech.FK.PeriodicPlanar
