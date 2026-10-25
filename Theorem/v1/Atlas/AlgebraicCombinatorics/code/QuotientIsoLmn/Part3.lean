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
import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part4
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

lemma card_eq_of_sameOrbit {S T : Finset (Fin m × Fin n)}
    (h : WreathOrbits.SameOrbit S T) : S.card = T.card := by
  obtain ⟨g, rfl⟩ := h
  exact (Finset.card_image_of_injective _ g.actOn_injective).symm

end QuotientIsoLmn
