/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Inductive.StatisticalMechanics.Code.Inequalities.OSSS
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


namespace DecisionTree

def eval : DecisionTree E → ConfigSpace E → Bool
  | leaf b, _ => b
  | node e t f, ω => if ω e then eval t ω else eval f ω


def queried : DecisionTree E → ConfigSpace E → Finset E
  | leaf _, _ => ∅
  | node e t f, ω => insert e (if ω e then queried t ω else queried f ω)


noncomputable def evalR (T : DecisionTree E) (ω : ConfigSpace E) : ℝ :=
  if T.eval ω then 1 else 0

end DecisionTree
end OSSS
end StatMech
