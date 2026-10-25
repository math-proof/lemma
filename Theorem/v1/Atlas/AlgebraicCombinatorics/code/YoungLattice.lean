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
import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice
set_option autoImplicit false

open SpernerProperty


namespace YoungLattice

namespace Lmn

@[ext]
lemma ext {m n : ℕ} {p q : Lmn m n} (h : ∀ i, p.val i = q.val i) : p = q :=
  Subtype.ext (funext h)

end Lmn
end YoungLattice
