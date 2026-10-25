/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


@[simp] theorem axisSwapCoordinates_apply (x : Fin 2 → Real) (i : Fin 2) :
    axisSwapCoordinates x i = x (Fin.rev i) := by
  change (Equiv.piCongrLeft (fun _ : Fin 2 => Real) Fin.revPerm) x i =
    x (Fin.rev i)
  simpa using (Equiv.piCongrLeft_apply_apply
    (P := fun _ : Fin 2 => Real) Fin.revPerm x (Fin.rev i))


end StatMech.FK.PeriodicPlanar
