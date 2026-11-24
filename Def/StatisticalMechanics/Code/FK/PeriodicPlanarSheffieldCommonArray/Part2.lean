module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryGrid
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGridAssembly
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonArray
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


def boundaryGridBase (baseLeft baseBottom : Site 2) : Site 2 :=
  fun i => if i = 0 then baseLeft 0 else baseBottom 1

end StatMech.FK.PeriodicPlanar
