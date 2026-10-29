/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestConclusion.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability
open Set
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def raiseFields (xi : NonnegativeField d) (S : Finset (Site d))
    (r : Site d → NNReal) : NonnegativeField d :=
  fun y => if y ∈ S then max (r y) (xi y) else xi y

end StatMech.FrontierA
