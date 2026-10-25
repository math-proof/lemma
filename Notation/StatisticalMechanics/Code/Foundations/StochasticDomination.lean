/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StochasticDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Foundations.StochasticDomination
open MeasureTheory


namespace StatMech

variable {E : Type*}


@[inherit_doc]
scoped infix:50 " ≼ " => StochasticallyDominated


end StatMech
