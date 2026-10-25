/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Def.StatisticalMechanics.Code.OSSS.LindebergTree
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace LindebergTree

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg

open OSSS.DecisionTree

section Path

variable {E : Type*} [DecidableEq E]


@[simp] lemma pathPrefix_leaf (b : Bool) (ω : ConfigSpace E) (t : ℕ) :
    pathPrefix (leaf b) ω t = ∅ := by cases t <;> rfl

@[simp] lemma pathPrefix_zero (T : DecisionTree E) (ω : ConfigSpace E) :
    pathPrefix T ω 0 = ∅ := by cases T <;> rfl

lemma pathPrefix_node_succ (e : E) (t f : DecisionTree E) (ω : ConfigSpace E) (k : ℕ) :
    pathPrefix (node e t f) ω (k + 1)
      = insert e (pathPrefix (if ω e then t else f) ω k) := rfl


end Path
end LindebergTree
end OSSS
end StatMech
