/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonPlusLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.MagNonneg.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Def.StatisticalMechanics.Code.Sharpness.SimonPlusLimit
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


@[simp] theorem spinPairBCF_apply (x y : Site d)
    (ω : ConfigSpace (Site d)) :
    spinPairBCF x y ω = spin ω x * spin ω y := rfl


end Sharpness
end StatMech
