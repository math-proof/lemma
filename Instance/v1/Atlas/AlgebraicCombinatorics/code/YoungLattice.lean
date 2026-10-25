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
import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice
set_option autoImplicit false

open SpernerProperty


namespace YoungLattice

namespace Lmn

instance instPartialOrder (m n : ℕ) : PartialOrder (Lmn m n) :=
  Subtype.partialOrder _

noncomputable instance instDecidableEq (m n : ℕ) : DecidableEq (Lmn m n) :=
  Classical.decEq _

noncomputable instance instFintype (m n : ℕ) : Fintype (Lmn m n) := by
  classical
  exact Fintype.subtype (Finset.univ.filter (fun f : Fin m → Fin (n + 1) => Antitone f))
    (fun f => by simp [Finset.mem_filter])

end Lmn
end YoungLattice
