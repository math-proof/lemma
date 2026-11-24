module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.QuotientPoset
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanSperner
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanUpDown
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.OrderRaisingLemma
public import Def.v1.Atlas.AlgebraicCombinatorics.code.BooleanSperner
public import Def.v1.Atlas.AlgebraicCombinatorics.code.BooleanUpDown
public import Def.v1.Atlas.AlgebraicCombinatorics.code.OrderRaisingLemma
public import Def.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
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
