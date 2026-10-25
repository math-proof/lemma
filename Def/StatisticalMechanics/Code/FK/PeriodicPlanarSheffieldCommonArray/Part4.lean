/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryGrid
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGridAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonArray.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def boundaryGridWidth
    (extent : Nat) (baseLeft baseRight : Site 2) : Nat :=
  (baseRight 0 + (extent : Int) - baseLeft 0).toNat


def boundaryGridHeight
    (extent : Nat) (baseBottom baseTop : Site 2) : Nat :=
  (baseTop 1 + (extent : Int) - baseBottom 1).toNat

end StatMech.FK.PeriodicPlanar
