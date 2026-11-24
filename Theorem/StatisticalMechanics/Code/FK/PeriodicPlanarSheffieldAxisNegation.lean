module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNearBoundary
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation
open Filter MeasureTheory Set SimpleGraph Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean -/
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

@[simp] theorem siteNeg_zero : siteNeg (0 : Site 2) = 0 := neg_zero

@[simp] theorem siteNeg_add (z w : Site 2) :
    siteNeg (z + w) = siteNeg z + siteNeg w := by
  simp [siteNeg, add_comm]

@[simp] theorem siteNeg_neg (z : Site 2) : siteNeg (siteNeg z) = z := by
  simp [siteNeg]

end StatMech.FK.PeriodicPlanar
