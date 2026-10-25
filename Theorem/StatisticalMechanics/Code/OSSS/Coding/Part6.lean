/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Coding.Part6
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


open OSSS.DecisionTree

omit [Fintype E] in


lemma stoppingTime_eq_card (T : DecisionTree E) (ω : ConfigSpace E) :
    stoppingTime T ω = (T.queried ω).card := rfl

omit [Fintype E] in


lemma eval_determined_by_queried (T : DecisionTree E) (ω ω' : ConfigSpace E)
    (h : ∀ e ∈ T.queried ω, ω' e = ω e) : T.eval ω' = T.eval ω :=
  eval_eq_of_agree_on_queried T ω ω' h

end OSSS.Coding
end StatMech
