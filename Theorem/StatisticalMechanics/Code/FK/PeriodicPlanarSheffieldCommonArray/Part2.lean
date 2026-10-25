/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryGrid
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGridAssembly
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonArray.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


@[simp] theorem boundaryGridBase_zero_apply
    (baseLeft baseBottom : Site 2) :
    boundaryGridBase baseLeft baseBottom 0 = baseLeft 0 := by
  simp [boundaryGridBase]

@[simp] theorem boundaryGridBase_one_apply
    (baseLeft baseBottom : Site 2) :
    boundaryGridBase baseLeft baseBottom 1 = baseBottom 1 := by
  simp [boundaryGridBase]


end StatMech.FK.PeriodicPlanar
