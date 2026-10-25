/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def cov (ν : E → Bool → ℝ) (f g : ConfigSpace E → ℝ) : ℝ :=
  expect ν (fun ω => f ω * g ω) - expect ν f * expect ν g


noncomputable def var (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ := cov ν g g


noncomputable def infl (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) (e : E) : ℝ :=
  expect ν (fun ω => |g (setOpen e ω) - g (setClosed e ω)|)


noncomputable def condMean (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ) :
    ConfigSpace E → ℝ :=
  fun ω => ν e true * g (setOpen e ω) + ν e false * g (setClosed e ω)

end OSSS
end StatMech
