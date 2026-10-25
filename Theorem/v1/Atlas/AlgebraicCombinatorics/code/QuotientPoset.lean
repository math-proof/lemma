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
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset
open Finset MulAction
open scoped Pointwise


namespace SpernerProperty

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

theorem card_eq_of_orbitRel {S T : Finset (Fin n)}
    (h : (orbitRel G (Finset (Fin n))).r S T) :
    S.card = T.card := by
  rw [orbitRel_apply] at h
  obtain ⟨g, hg⟩ := h
  rw [← hg]
  exact Finset.card_smul_finset g T

theorem card_eq_of_mk_eq {S T : Finset (Fin n)}
    (h : (Quotient.mk (orbitRel G (Finset (Fin n))) S) =
         (Quotient.mk (orbitRel G (Finset (Fin n))) T)) :
    S.card = T.card :=
  card_eq_of_orbitRel (Quotient.exact h)

end SpernerProperty
