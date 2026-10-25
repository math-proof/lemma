/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WreathOrbits
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

instance : PartialOrder (GridYoungDiagram m n) where
  le S T := S.val ⊆ T.val
  le_refl S := Finset.Subset.refl S.val
  le_trans _ _ _ hab hbc := Finset.Subset.trans hab hbc
  le_antisymm S T hST hTS := Subtype.ext (Finset.Subset.antisymm hST hTS)

end QuotientIsoLmn
