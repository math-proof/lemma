/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QuotientPoset
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanSperner
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanUpDown
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.OrderRaisingLemma
import Def.v1.Atlas.AlgebraicCombinatorics.code.BooleanSperner
import Def.v1.Atlas.AlgebraicCombinatorics.code.BooleanUpDown
import Def.v1.Atlas.AlgebraicCombinatorics.code.OrderRaisingLemma
import Instance.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
set_option autoImplicit false


noncomputable section

open scoped Classical Pointwise

open SpernerProperty MulAction Finset

namespace GroupActions

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

section EdgeAction

variable {m : ℕ}

lemma card_edgeSubsets (m : ℕ) : Fintype.card (EdgeSubsets m) = edgeCount m := by
  classical
  rw [Fintype.card_congr edgeSubsetsPowersetEquiv, Fintype.card_coe, edgeCount,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end EdgeAction
end GroupActions
end
