/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part7
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QuotientIsoLmn
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.GroupActions
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
set_option autoImplicit false


noncomputable section

open scoped Classical Pointwise

open SpernerProperty YoungLattice YoungLattice.Lmn

open QuotientIsoLmn GroupActions WreathOrbits Finset MulAction

namespace YoungLattice.Lmn

variable {m n : ℕ}

def wreathElemToPerm (g : WreathElem m n) : Equiv.Perm (Fin m × Fin n) :=
  Equiv.ofBijective g.actOn g.actOn_injective.bijective_of_finite

noncomputable def wreathSubgroup (m n : ℕ) : Subgroup (Equiv.Perm (Fin (m * n))) :=
  Subgroup.closure
    {π | ∃ g : WreathElem m n,
      π = finProdFinEquiv.permCongr (wreathElemToPerm g)}

end YoungLattice.Lmn
end
