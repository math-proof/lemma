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
import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset
open Finset MulAction
open scoped Pointwise


namespace SpernerProperty

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

@[simp]
theorem quotientPosetRank_mk (S : Finset (Fin n)) :
    quotientPosetRank n G (Quotient.mk _ S) = S.card :=
  rfl

theorem quotientPosetRank_le (q : QuotientPoset n G) :
    quotientPosetRank n G q ≤ n := by
  induction q using Quotient.inductionOn with
  | _ S =>
    simp only [quotientPosetRank_mk]
    exact (Finset.card_le_univ S).trans (Fintype.card_fin n).le

theorem quotientPosetRank_univ :
    quotientPosetRank n G (Quotient.mk _ Finset.univ) = n := by
  simp only [quotientPosetRank_mk, Finset.card_univ, Fintype.card_fin]

section Order

theorem mk_smul_eq (g : G) (S : Finset (Fin n)) :
    Quotient.mk (orbitRel G (Finset (Fin n))) (g • S) =
    Quotient.mk (orbitRel G (Finset (Fin n))) S := by
  apply Quotient.sound
  show g • S ∈ orbit G S
  exact ⟨g, rfl⟩

end Order
end SpernerProperty
