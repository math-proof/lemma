module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.QuotientPoset
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanSperner
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanUpDown
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.OrderRaisingLemma
public import Def.v1.Atlas.AlgebraicCombinatorics.code.BooleanSperner
public import Def.v1.Atlas.AlgebraicCombinatorics.code.BooleanUpDown
public import Def.v1.Atlas.AlgebraicCombinatorics.code.OrderRaisingLemma
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.GroupActions.Part2
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

noncomputable def edgeBij (m : ℕ) : EdgeSubsets m ≃ Fin (edgeCount m) :=
  Fintype.equivFinOfCardEq (card_edgeSubsets m)

noncomputable def edgeActionHom (m : ℕ) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin (edgeCount m)) :=
  ((edgeBij m).permCongrHom).toMonoidHom.comp
    (MulAction.toPermHom (Equiv.Perm (Fin m)) (EdgeSubsets m))

end EdgeAction

noncomputable def graphIsoGroup (m : ℕ) : Subgroup (Equiv.Perm (Fin (edgeCount m))) :=
  (edgeActionHom m).range

end GroupActions
end
