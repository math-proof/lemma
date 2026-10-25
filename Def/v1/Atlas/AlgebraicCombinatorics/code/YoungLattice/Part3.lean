/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.Order.Cover
import Mathlib.Order.Grade
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
set_option autoImplicit false

open SpernerProperty


namespace YoungLattice

namespace Lmn

def complement {m n : ℕ} (p : Lmn m n) : Lmn m n :=
  ⟨fun i => ⟨n - (p.val (Fin.rev i)).val, by omega⟩,
   fun a b hab => by
    simp only [Fin.le_def]
    have := p.property (Fin.rev_le_rev.mpr hab); omega⟩

end Lmn
end YoungLattice
