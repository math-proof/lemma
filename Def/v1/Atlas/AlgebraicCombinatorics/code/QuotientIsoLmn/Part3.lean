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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

def lmnToGridYoung (p : Lmn m n) : GridYoungDiagram m n :=
  ⟨lmnToFinset p, lmnToFinset_isGridYoung p⟩

def gridYoungToLmn (S : GridYoungDiagram m n) : Lmn m n :=
  ⟨fun i => ⟨WreathOrbits.rowSize S.val i,
             Nat.lt_succ_of_le (WreathOrbits.rowSize_le S.val i)⟩,
   fun i j hij => S.property.2 hij⟩

end QuotientIsoLmn
