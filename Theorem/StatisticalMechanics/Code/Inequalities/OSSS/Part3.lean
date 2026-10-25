/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.Inequalities.OSSS.Part4
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


namespace DecisionTree

omit [Fintype E] [DecidableEq E] in

lemma evalR_le_one (T : DecisionTree E) (ω : ConfigSpace E) : T.evalR ω ≤ 1 := by
  unfold evalR; split <;> norm_num

omit [Fintype E] [DecidableEq E] in

lemma evalR_nonneg (T : DecisionTree E) (ω : ConfigSpace E) : 0 ≤ T.evalR ω := by
  unfold evalR; split <;> norm_num

omit [Fintype E] in


lemma abs_evalR_diff_le_one (T : DecisionTree E) (e : E) (ω : ConfigSpace E) :
    |T.evalR (setOpen e ω) - T.evalR (setClosed e ω)| ≤ 1 := by
  have h1 := evalR_le_one T (setOpen e ω)
  have h2 := evalR_nonneg T (setOpen e ω)
  have h3 := evalR_le_one T (setClosed e ω)
  have h4 := evalR_nonneg T (setClosed e ω)
  rw [abs_le]; constructor <;> linarith

end DecisionTree
end OSSS
end StatMech
