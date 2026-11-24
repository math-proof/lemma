module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.QuotientPoset
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanSperner
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanUpDown
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.OrderRaisingLemma
public import Def.v1.Atlas.AlgebraicCombinatorics.code.BooleanSperner
public import Def.v1.Atlas.AlgebraicCombinatorics.code.BooleanUpDown
public import Def.v1.Atlas.AlgebraicCombinatorics.code.OrderRaisingLemma
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
set_option autoImplicit false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
