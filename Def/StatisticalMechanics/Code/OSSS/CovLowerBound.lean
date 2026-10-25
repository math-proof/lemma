/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Poincare.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.CovLowerBound

open StatMech.OSSS

open StatMech.OSSS.Poincare

open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {ν : E → Bool → ℝ}


noncomputable def coordI (e : E) : ConfigSpace E → ℝ := fun ω => if ω e then (1 : ℝ) else 0

end OSSS.CovLowerBound
end StatMech
