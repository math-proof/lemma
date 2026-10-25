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
import Def.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
set_option autoImplicit false


noncomputable section

open scoped Classical Pointwise

open SpernerProperty MulAction Finset

namespace GroupActions

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

section EdgeAction

variable {m : ℕ}

noncomputable instance edgeSubsets_mulAction :
    MulAction (Equiv.Perm (Fin m)) (EdgeSubsets m) where
  smul σ e := ⟨σ • e.val, by rw [Finset.card_smul_finset]; exact e.prop⟩
  one_smul e := Subtype.ext (one_smul _ e.val)
  mul_smul σ τ e := Subtype.ext (mul_smul σ τ e.val)

noncomputable instance edgeSubsets_fintype : Fintype (EdgeSubsets m) := by
  classical
  exact Fintype.ofEquiv _ edgeSubsetsPowersetEquiv.symm

end EdgeAction
end GroupActions
end
