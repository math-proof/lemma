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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset.Part3
open Finset MulAction
open scoped Pointwise


namespace SpernerProperty

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

noncomputable instance quotientPoset_gradeMinOrder (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    GradeMinOrder ℕ (QuotientPoset n G) where
  grade := quotientPosetRank n G
  grade_strictMono := quotientPosetRank_strictMono n G
  covBy_grade _ _ := quotientPosetRank_covBy n G
  isMin_grade _ := quotientPosetRank_isMin n G

noncomputable instance quotientPoset_gradedPoset (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    letI := quotientPoset_gradeMinOrder n G
    GradedPoset (QuotientPoset n G) where
  rank := n
  grade_le_rank a := by
    change quotientPosetRank n G a ≤ n
    exact quotientPosetRank_le a
  grade_rank_exists := by
    refine ⟨Quotient.mk _ Finset.univ, ?_⟩
    change quotientPosetRank n G (Quotient.mk _ Finset.univ) = n
    exact quotientPosetRank_univ

end SpernerProperty
