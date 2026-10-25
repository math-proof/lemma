/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryGrid
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGridAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonArray.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def boundaryGridLeftShift (baseLeft baseBottom : Site 2) : Site 2 :=
  verticalShift (baseBottom 1 - baseLeft 1)


def boundaryGridBottomShift (baseLeft baseBottom : Site 2) : Site 2 :=
  horizontalShift (baseLeft 0 - baseBottom 0)


def boundaryGridRightShift
    (extent : Int) (baseRight baseBottom : Site 2) : Site 2 :=
  horizontalShift extent + verticalShift (baseBottom 1 - baseRight 1)


def boundaryGridTopShift
    (extent : Int) (baseLeft baseTop : Site 2) : Site 2 :=
  horizontalShift (baseLeft 0 - baseTop 0) + verticalShift extent

end StatMech.FK.PeriodicPlanar
