/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part2
open MeasureTheory
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


@[simp] theorem raiseField_self (xi : NonnegativeField d) (x : Site d) (r : ℝ≥0) :
    raiseField xi x r x = max r (xi x) := by
  simp [raiseField]

@[simp] theorem raiseField_apply_of_ne (xi : NonnegativeField d)
    {x y : Site d} (h : y ≠ x) (r : ℝ≥0) :
    raiseField xi x r y = xi y := by
  simp [raiseField, h]


end StatMech.FrontierA
