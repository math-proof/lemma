/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryGrid
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGridAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonArray
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def boundaryGridBase (baseLeft baseBottom : Site 2) : Site 2 :=
  fun i => if i = 0 then baseLeft 0 else baseBottom 1

end StatMech.FK.PeriodicPlanar
