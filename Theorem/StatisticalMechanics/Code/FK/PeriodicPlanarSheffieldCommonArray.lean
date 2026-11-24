module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryGrid
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGridAssembly
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonArray
open Filter MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


@[simp] theorem horizontalShift_zero_apply (t : Int) :
    horizontalShift t 0 = t := by
  simp [horizontalShift]

@[simp] theorem horizontalShift_one_apply (t : Int) :
    horizontalShift t 1 = 0 := by
  simp [horizontalShift]


end StatMech.FK.PeriodicPlanar
