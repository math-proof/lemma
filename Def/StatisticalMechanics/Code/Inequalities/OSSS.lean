/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def weight (ν : E → Bool → ℝ) (ω : ConfigSpace E) : ℝ := ∏ e, ν e (ω e)


noncomputable def expect (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, weight ν ω * g ω


end OSSS
end StatMech
