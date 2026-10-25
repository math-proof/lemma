/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryGrid
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGridAssembly
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonArray.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


@[simp] theorem boundaryGridLeftShift_zero_apply
    (baseLeft baseBottom : Site 2) :
    boundaryGridLeftShift baseLeft baseBottom 0 = 0 := by
  simp [boundaryGridLeftShift]

@[simp] theorem boundaryGridBottomShift_one_apply
    (baseLeft baseBottom : Site 2) :
    boundaryGridBottomShift baseLeft baseBottom 1 = 0 := by
  simp [boundaryGridBottomShift]

@[simp] theorem boundaryGridRightShift_zero_apply
    (extent : Int) (baseRight baseBottom : Site 2) :
    boundaryGridRightShift extent baseRight baseBottom 0 = extent := by
  simp [boundaryGridRightShift]

@[simp] theorem boundaryGridTopShift_one_apply
    (extent : Int) (baseLeft baseTop : Site 2) :
    boundaryGridTopShift extent baseLeft baseTop 1 = extent := by
  simp [boundaryGridTopShift]


end StatMech.FK.PeriodicPlanar
