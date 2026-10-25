/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


@[simp] theorem siteAxisSwap_zero : siteAxisSwap (0 : Site 2) = 0 := by
  rfl

@[simp] theorem siteAxisSwap_add (z w : Site 2) :
    siteAxisSwap (z + w) = siteAxisSwap z + siteAxisSwap w := by
  rfl

@[simp] theorem siteAxisSwap_swap (z : Site 2) :
    siteAxisSwap (siteAxisSwap z) = z := by
  ext i
  simp [siteAxisSwap]

end StatMech.FK.PeriodicPlanar
