module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryGrid
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGridAssembly
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


def horizontalShift (t : Int) : Site 2 :=
  fun i => if i = 0 then t else 0

end StatMech.FK.PeriodicPlanar
