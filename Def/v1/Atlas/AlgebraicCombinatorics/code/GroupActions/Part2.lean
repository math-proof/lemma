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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.GroupActions.Part2
set_option autoImplicit false


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
