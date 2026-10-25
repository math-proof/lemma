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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part6
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

noncomputable def wreathQuotientIsoGridYoung (m n : ℕ) :
    WreathQuotient m n ≃o GridYoungDiagram m n where
  toFun := wreathQuotientToGridYoung
  invFun := gridYoungToWreathQuotient
  left_inv := gridYoungToWreathQuotient_wreathQuotientToGridYoung
  right_inv := wreathQuotientToGridYoung_gridYoungToWreathQuotient
  map_rel_iff' := wreathQuotientToGridYoung_le_iff _ _

noncomputable def wreathQuotientIsoLmn (m n : ℕ) :
    WreathQuotient m n ≃o Lmn m n :=
  (wreathQuotientIsoGridYoung m n).trans (quotientIsoLmn m n)

end QuotientIsoLmn
