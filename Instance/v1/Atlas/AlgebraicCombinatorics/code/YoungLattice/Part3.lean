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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part4
set_option autoImplicit false

open SpernerProperty


namespace YoungLattice

namespace Lmn

instance instGradedPoset (m n : ℕ) : GradedPoset (Lmn m n) where
  rank := m * n
  grade_le_rank := grade_le_mul
  grade_rank_exists := ⟨top m n, by rw [grade_eq, sumParts_top]⟩

end Lmn
end YoungLattice
