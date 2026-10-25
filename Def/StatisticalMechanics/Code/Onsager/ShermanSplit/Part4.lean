/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanSplit.Part3


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section Split

variable {E : Type*} [DecidableEq E]


def ons_isFirstReturnSegment (e : E) (s : List E) : Prop :=
  ∃ interior : List E,
    s = e :: interior ++ [e] ∧ ∀ x ∈ interior, x ≠ e

end Split
end StatMech.Onsager
