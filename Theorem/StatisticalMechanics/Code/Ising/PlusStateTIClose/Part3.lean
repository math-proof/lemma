/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTI.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexUncond
import Def.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


@[simp] theorem pstc_coordBcf_apply (x : Site d) (ω : ConfigSpace (Site d)) :
    pstc_coordBcf x ω = if ω x then (1 : ℝ) else 0 := rfl


end Ising
end StatMech
