/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInsertion
open MeasureTheory
open scoped ENNReal NNReal


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


def forceSiteOccupied (x : Site d) (eta : ConfigSpace (Site d)) :
    ConfigSpace (Site d) := fun y => if y = x then true else eta y

end StatMech.FrontierA
