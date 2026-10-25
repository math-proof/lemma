/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Finset.Card
import Instance.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset.Part2
open Finset MulAction
open scoped Pointwise


section RankSymmetry

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

theorem smul_compl_eq (g : G) (S : Finset (Fin n)) :
    g • (Finset.univ \ S) = Finset.univ \ (g • S) := by
  rw [smul_finset_sdiff, smul_finset_univ]

end RankSymmetry
