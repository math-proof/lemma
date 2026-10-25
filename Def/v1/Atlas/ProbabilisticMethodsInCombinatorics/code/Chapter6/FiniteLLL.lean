/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/FiniteLLL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.Card
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.LovaszLocalLemma
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter6.LovaszLocalLemma
open MeasureTheory ProbabilityTheory Set Finset ENNReal


noncomputable section

set_option maxHeartbeats 800000

namespace Beck

variable {α ι : Type*}

/-- Restrict a Boolean function on `α` to the subtype of elements lying in a finset `C`. -/
def restrictToSubtype [DecidableEq α] (C : Finset α) (f : α → Bool) : {a // a ∈ C} → Bool :=
  fun ⟨a, _⟩ => f a

end Beck
end
